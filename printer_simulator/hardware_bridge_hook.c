// fake_hardware_bridge.c
//
// Compile: gcc -shared -fPIC -o fake_hardware_bridge.so fake_hardware_bridge.c -ldl
// Usage:   LD_PRELOAD=./fake_hardware_bridge.so ./klipper.elf
//
// Opens a Socket in FAKE_HARDWARE_SOCKET and listens for requests to simulate ADC and GPIO.
// default GPIO Value is 0, default ADC value is 0 (12-bit: 0-4095). Requests are simple text commands:
//   GET analogN          → N=0..7 for ADC, Response is ADC value (0-4095)
//   GET chipN_gpioM     → N=Chip-Number, M=Pin-Number, Response is 0 or 1
//   SET chipN_gpioM V   → N=Chip-Number, M=Pin-Number, V=0 or 1, sets the GPIO value
#define _GNU_SOURCE
#include <dlfcn.h>
#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include <fcntl.h>
#include <unistd.h>
#include <errno.h>
#include <sys/ioctl.h>
#include <linux/gpio.h>

#include <sys/mman.h>
#include <time.h>
#include <poll.h>
#include <pthread.h>
#include <sched.h>
#include <signal.h>
#include <sys/syscall.h>
#include <sys/socket.h>
#include <sys/un.h>
#define MAX_FAKE_FDS 128
#define SOCKET_PATH_ENV "FAKE_HARDWARE_SOCKET"
#define SOCKET_TIMEOUT_MS 100

/*
Bridge overrides syscalls like open, ioctl, pread, access and close to intercept calls to ADC and GPIO devices.
For ADC: when Klipper tries to open /sys/bus/iio/devices/iio:device0/in_voltageN_raw, we return a dummy fd and track it as an ADC channel
For GPIO: when Klipper tries to open /dev/gpiochipN, we return a dummy fd and track it as a GPIO chip. 
Then we handle ioctls to provide chip info, line info, and line handle requests, and we track line handles to simulate GPIO reads/writes.
*/
static int   (*real_open)(const char*, int, ...)   = NULL;
static int   (*real_close)(int)                    = NULL;
static int   (*real_ioctl)(int, unsigned long, ...) = NULL;
static int   (*real_access)(const char*, int)      = NULL;
static ssize_t (*real_pread)(int, void*, size_t, off_t) = NULL;

static void init_real_funcs(void) {
    if (!real_open)   real_open   = dlsym(RTLD_NEXT, "open");
    if (!real_close)  real_close  = dlsym(RTLD_NEXT, "close");
    if (!real_ioctl)  real_ioctl  = dlsym(RTLD_NEXT, "ioctl");
    if (!real_access) real_access = dlsym(RTLD_NEXT, "access");
    if (!real_pread)  real_pread  = dlsym(RTLD_NEXT, "pread");
}


// ─────────────────────────────────────────────────────────
// FD Tracking
// ─────────────────────────────────────────────────────────

typedef enum { FD_NONE, FD_ADC, FD_GPIO_CHIP, FD_GPIO_LINE } FdType;

typedef struct {
    int    fd;
    FdType type;
    int    channel;                      // ADC: Channel Number
    int    chip;                         // GPIO: Chip Number
    int    line_offsets[GPIOHANDLES_MAX]; // GPIO Line: which Pins
    int    num_lines;
} FakeFd;

static FakeFd fake_fds[MAX_FAKE_FDS];

static FakeFd *find_fake_fd(int fd) {
    for (int i = 0; i < MAX_FAKE_FDS; i++)
        if (fake_fds[i].type != FD_NONE && fake_fds[i].fd == fd)
            return &fake_fds[i];
    return NULL;
}

static FakeFd *alloc_fake_fd(int fd, FdType type) {
    for (int i = 0; i < MAX_FAKE_FDS; i++) {
        if (fake_fds[i].type == FD_NONE) {
            memset(&fake_fds[i], 0, sizeof(FakeFd));
            fake_fds[i].fd   = fd;
            fake_fds[i].type = type;
            return &fake_fds[i];
        }
    }
    return NULL;
}

static void free_fake_fd(int fd) {
    FakeFd *f = find_fake_fd(fd);
    if (f) f->type = FD_NONE;
}

static int make_dummy_fd(void) {
    return real_open("/dev/null", O_RDONLY);
}



// ─────────────────────────────────────────────────────────
// Socket Communication
// ─────────────────────────────────────────────────────────

static int hw_debug(void) {
    static int dbg = -1;
    if (dbg < 0) dbg = getenv("FAKE_HW_DEBUG") != NULL;
    return dbg;
}

// Pin the MCU process in memory. "klipper.elf -r" would do this itself (mlockall together with
// SCHED_FIFO), but it exits on EPERM as user "printer", so scripts/start_mcu.sh only sets the
// priority with chrt. Without mlockall, pages of the idle MCU can be swapped out or reclaimed;
// the page fault on the next step then stalls the MCU for milliseconds and it shuts down with
// "Stepper too far in past". Needs a large enough memlock limit (docker-compose.yml: ulimits).
// Every hook call runs inside the MCU's timer loop. A call that takes a millisecond delays the
// next step; report such outliers so a stall can be told apart from one outside the hook.
#define SLOW_CALL_MS 1.0
static void probe_log(const char *fmt, ...);
static double hw_now_ms(void) {
    struct timespec t;
    clock_gettime(CLOCK_MONOTONIC, &t);
    return (double)t.tv_sec * 1e3 + (double)t.tv_nsec / 1e6;
}

static void hw_report_slow(const char *what, const char *key, double start_ms) {
    double ms = hw_now_ms() - start_ms;
    if (ms >= SLOW_CALL_MS)
        probe_log("slow %s %s: %.2f ms", what, key, ms);
}


// The LD_PRELOAD is inherited by every process start_mcu.sh spawns (bash, sudo, chrt, sleep);
// the constructors below must act only in the MCU itself.
static int hw_is_mcu(void) {
    extern char *program_invocation_short_name;
    return strcmp(program_invocation_short_name, "klipper.elf") == 0;
}

__attribute__((constructor(1001)))
static void hw_lock_memory(void) {
    if (!hw_is_mcu()) return;
    if (mlockall(MCL_CURRENT | MCL_FUTURE) == 0) {
        fprintf(stderr, "[fake_hw] MCU memory locked (mlockall)\n");
        return;
    }
    fprintf(stderr, "[fake_hw] mlockall failed: %s (raise the memlock ulimit, see docker-compose.yml)\n",
            strerror(errno));
}

// Persistent connection to the Python server: one socket for all requests instead of one
// connection (and one Python thread) per GPIO toggle, which was too slow for step pulses.
static int hw_sock = -1;
static void hw_reset_connection(void);

static int hw_connect(void) {
    if (hw_sock >= 0) return hw_sock;
    const char *socket_path = getenv(SOCKET_PATH_ENV);
    if (!socket_path) return -1;
    int sock = socket(AF_UNIX, SOCK_STREAM, 0);
    if (sock < 0) return -1;
    struct sockaddr_un addr = {0};
    addr.sun_family = AF_UNIX;
    strncpy(addr.sun_path, socket_path, sizeof(addr.sun_path) - 1);
    if (connect(sock, (struct sockaddr*)&addr, sizeof(addr)) < 0) {
        close(sock);
        return -1;
    }
    struct timeval tv = { .tv_sec = 0, .tv_usec = SOCKET_TIMEOUT_MS * 1000 };
    setsockopt(sock, SOL_SOCKET, SO_RCVTIMEO, &tv, sizeof(tv));
    hw_sock = sock;
    return hw_sock;
}

// Outgoing messages are queued here and sent without ever blocking the MCU. A unix socket
// accounts ~1 KB of kernel memory per small send, so its buffer holds only a few hundred
// step messages; a short stall of the Python server then blocked send() and the MCU
// missed its step times. The queue absorbs such stalls (1 MB = tens of thousands of steps).
static char hw_wbuf[1 << 20];
static size_t hw_wlen = 0;

static void hw_flush(void) {
    int sock = hw_connect();
    if (sock < 0) return;
    size_t off = 0;
    while (off < hw_wlen) {
        ssize_t n = send(sock, hw_wbuf + off, hw_wlen - off, MSG_NOSIGNAL | MSG_DONTWAIT);
        if (n > 0) { off += (size_t)n; continue; }
        if (n < 0 && (errno == EAGAIN || errno == EWOULDBLOCK || errno == EINTR)) break;
        hw_reset_connection();
        return;
    }
    memmove(hw_wbuf, hw_wbuf + off, hw_wlen - off);
    hw_wlen -= off;
}

static int hw_send(const char *msg) {
    size_t len = strlen(msg);
    if (hw_wlen + len > sizeof(hw_wbuf)) hw_flush();
    if (hw_wlen + len > sizeof(hw_wbuf)) return -1;  // simulator far behind: drop the message
    memcpy(hw_wbuf + hw_wlen, msg, len);
    hw_wlen += len;
    hw_flush();
    return hw_sock;
}

// Input values (endstops, ADC, sensors) are cached in the hook. The first read of a key
// subscribes to it ("SUB key"); from then on the server pushes "VAL key value" whenever the
// value changes. Reads never wait for Python, so the MCU's step timers are never delayed.
#define MAX_CACHED 64
static struct { char key[32]; int value; } hw_cache[MAX_CACHED];
static int hw_cache_len = 0;
static char hw_rbuf[8192];
static size_t hw_rlen = 0;

static int cache_find(const char *key) {
    for (int i = 0; i < hw_cache_len; i++)
        if (strcmp(hw_cache[i].key, key) == 0) return i;
    return -1;
}

static void cache_store(const char *key, int value) {
    int i = cache_find(key);
    if (i < 0) {
        if (hw_cache_len >= MAX_CACHED) return;
        i = hw_cache_len++;
        snprintf(hw_cache[i].key, sizeof(hw_cache[i].key), "%s", key);
    }
    hw_cache[i].value = value;
}

static void hw_reset_connection(void) {
    if (hw_sock >= 0) close(hw_sock);
    hw_sock = -1;
    hw_rlen = 0;
    hw_wlen = 0;
    hw_cache_len = 0;  // resubscribe after a reconnect
}

// Read whatever the server has pushed and update the cache. With wait_ms > 0 block up to that
// long for the first data (only used for the initial subscription of a key).
static void hw_poll(int wait_ms) {
    if (hw_wlen) hw_flush();  // also drain queued messages when nothing new is written
    int sock = hw_connect();
    if (sock < 0) return;
    for (;;) {
        int flags = MSG_DONTWAIT;
        if (wait_ms > 0) {
            struct timeval tv = { .tv_sec = wait_ms / 1000, .tv_usec = (wait_ms % 1000) * 1000 };
            setsockopt(sock, SOL_SOCKET, SO_RCVTIMEO, &tv, sizeof(tv));
            flags = 0;
        }
        if (hw_rlen >= sizeof(hw_rbuf) - 1) hw_rlen = 0;  // overlong garbage, drop it
        ssize_t r = recv(sock, hw_rbuf + hw_rlen, sizeof(hw_rbuf) - 1 - hw_rlen, flags);
        if (r == 0) { hw_reset_connection(); return; }
        if (r < 0) return;  // nothing (more) to read right now
        hw_rlen += (size_t)r;
        size_t start = 0;
        for (size_t i = 0; i < hw_rlen; i++) {
            if (hw_rbuf[i] != '\n') continue;
            hw_rbuf[i] = '\0';
            char key[32];
            int value;
            if (sscanf(hw_rbuf + start, "VAL %31s %d", key, &value) == 2) cache_store(key, value);
            start = i + 1;
        }
        memmove(hw_rbuf, hw_rbuf + start, hw_rlen - start);
        hw_rlen -= start;
        if (wait_ms > 0) return;
    }
}

static int read_value(const char *key, int fallback) {
    hw_poll(0);
    int i = cache_find(key);
    if (i >= 0) return hw_cache[i].value;
    // first read of this key: subscribe and wait for the initial value (only at startup)
    char request[64];
    snprintf(request, sizeof(request), "SUB %s\n", key);
    if (hw_send(request) < 0) return fallback;
    for (int attempt = 0; attempt < 20 && (i = cache_find(key)) < 0; attempt++) {
        hw_flush();
        hw_poll(SOCKET_TIMEOUT_MS);
    }
    return i >= 0 ? hw_cache[i].value : fallback;
}

static void write_value(const char *key, int value) {
    // fire-and-forget: the server does not answer SETQ, the MCU does not wait
    char request[64];
    snprintf(request, sizeof(request), "SETQ %s %d\n", key, value);
    hw_send(request);
    hw_poll(0);  // keep pushed values flowing so the server never blocks on a full socket
}




// ─────────────────────────────────────────────────────────
// Stall probe (debug): where does the MCU lose milliseconds?
//
// The MCU still shuts down with "Stepper too far in past" although no hook call
// takes longer than 1 ms, the process is locked in memory, runs with SCHED_FIFO
// and never waits for a CPU. So the time is lost either while the MCU sleeps in
// ppoll() waiting for its alarm, or in a system call the hook does not time, or
// on the CPU itself. This probe watches all three:
//  - ppoll() and timer_settime() are wrapped: a wake-up more than 1 ms after the
//    armed alarm is reported as "late wake"
//  - read()/write() on the pty are timed like the hook calls ("slow write")
//  - a watchdog thread on the same CPU ticks every 1 ms. It reports when it is
//    woken late itself (CPU or system stall) and when the main thread has made no
//    progress for 5 ms while not asleep; then it samples the main thread's state
//    and current system call from /proc so the stall can be located.
// All lines carry the CLOCK_MONOTONIC time, the same clock klippy.log uses.
// ─────────────────────────────────────────────────────────

static int (*real_ppoll)(struct pollfd*, nfds_t, const struct timespec*, const sigset_t*) = NULL;
static int (*real_timer_settime)(timer_t, int, const struct itimerspec*, struct itimerspec*) = NULL;
static ssize_t (*real_write)(int, const void*, size_t) = NULL;
static ssize_t (*real_read)(int, void*, size_t) = NULL;

static void init_probe_funcs(void) {
    if (!real_ppoll) real_ppoll = dlsym(RTLD_NEXT, "ppoll");
    if (!real_timer_settime) real_timer_settime = dlsym(RTLD_NEXT, "timer_settime");
    if (!real_write) real_write = dlsym(RTLD_NEXT, "write");
    if (!real_read) real_read = dlsym(RTLD_NEXT, "read");
    init_real_funcs();
}

static pid_t probe_main_tid;
static int probe_main_cpu = -1;
static volatile long probe_armed_ns;        // absolute CLOCK_MONOTONIC alarm the MCU waits for, 0 = none
static volatile long probe_sleep_since_ns;  // > 0 while the main thread sits in ppoll()
static volatile long probe_progress_ns;     // last time the main thread passed a probe point

static long probe_now_ns(void) {
    struct timespec t;
    clock_gettime(CLOCK_MONOTONIC, &t);
    return t.tv_sec * 1000000000L + t.tv_nsec;
}

// Log line with monotonic timestamp; writes through real_write so that the write()
// wrapper below is never re-entered.
static void probe_log(const char *fmt, ...) {
    char buf[512];
    long t = probe_now_ns();
    int n = snprintf(buf, sizeof(buf), "[fake_hw] %ld.%06ld ", t / 1000000000L, (t % 1000000000L) / 1000);
    va_list ap;
    va_start(ap, fmt);
    n += vsnprintf(buf + n, sizeof(buf) - (size_t)n, fmt, ap);
    va_end(ap);
    if (n > (int)sizeof(buf) - 2) n = (int)sizeof(buf) - 2;
    buf[n++] = '\n';
    ssize_t (*w)(int, const void*, size_t) = real_write ? real_write : write;
    w(2, buf, (size_t)n);
}

int ppoll(struct pollfd *fds, nfds_t nfds, const struct timespec *timeout, const sigset_t *sigmask) {
    init_probe_funcs();
    long t0 = probe_now_ns();
    probe_progress_ns = t0;
    probe_sleep_since_ns = t0;
    int ret = real_ppoll(fds, nfds, timeout, sigmask);
    int saved_errno = errno;
    long t1 = probe_now_ns();
    probe_sleep_since_ns = 0;
    probe_progress_ns = t1;
    long armed = probe_armed_ns;
    if (armed > 1000000L && t1 - armed > 1000000L)
        probe_log("late wake: %.2f ms after the alarm (slept %.2f ms, alarm was %s ppoll, ret=%d)",
                  (t1 - armed) / 1e6, (t1 - t0) / 1e6, armed < t0 ? "already due before" : "set before", ret);
    errno = saved_errno;
    return ret;
}

int timer_settime(timer_t timerid, int flags, const struct itimerspec *value, struct itimerspec *ovalue) {
    init_probe_funcs();
    if (value) {
        long target = value->it_value.tv_sec * 1000000000L + value->it_value.tv_nsec;
        if (target && !(flags & TIMER_ABSTIME)) target += probe_now_ns();
        probe_armed_ns = target;
    }
    probe_progress_ns = probe_now_ns();
    return real_timer_settime(timerid, flags, value, ovalue);
}

ssize_t write(int fd, const void *buf, size_t count) {
    init_probe_funcs();
    long t0 = probe_now_ns();
    ssize_t ret = real_write(fd, buf, count);
    int saved_errno = errno;
    long t1 = probe_now_ns();
    probe_progress_ns = t1;
    if (t1 - t0 > 1000000L && fd > 2)
        probe_log("slow write fd=%d: %.2f ms (ret=%zd)", fd, (t1 - t0) / 1e6, ret);
    errno = saved_errno;
    return ret;
}

ssize_t read(int fd, void *buf, size_t count) {
    init_probe_funcs();
    long t0 = probe_now_ns();
    ssize_t ret = real_read(fd, buf, count);
    int saved_errno = errno;
    long t1 = probe_now_ns();
    probe_progress_ns = t1;
    if (t1 - t0 > 1000000L && fd > 2)
        probe_log("slow read fd=%d: %.2f ms (ret=%zd)", fd, (t1 - t0) / 1e6, ret);
    errno = saved_errno;
    return ret;
}

// Read one small /proc file of the main thread (state letter from stat, or the syscall line).
static void probe_read_proc(const char *what, char *out, size_t outlen) {
    char path[64];
    snprintf(path, sizeof(path), "/proc/self/task/%d/%s", (int)probe_main_tid, what);
    out[0] = '\0';
    int fd = real_open(path, O_RDONLY);
    if (fd < 0) return;
    ssize_t n = real_read(fd, out, outlen - 1);
    real_close(fd);
    if (n < 0) n = 0;
    out[n] = '\0';
    for (char *c = out; *c; c++) if (*c == '\n') *c = ' ';
}

static char probe_state(void) {
    char buf[256];
    probe_read_proc("stat", buf, sizeof(buf));
    char *p = strrchr(buf, ')');
    return (p && p[1] == ' ') ? p[2] : '?';
}

static void *probe_watchdog(void *arg) {
    int cpu = (int)(long)arg;
    // SIGALRM is the MCU's alarm and process-directed; if it lands on this thread the main
    // thread keeps sleeping in ppoll. Block it here so the kernel always delivers it to main.
    sigset_t alarm;
    sigemptyset(&alarm);
    sigaddset(&alarm, SIGALRM);
    pthread_sigmask(SIG_BLOCK, &alarm, NULL);
    cpu_set_t set;
    CPU_ZERO(&set);
    CPU_SET(cpu, &set);
    sched_setaffinity(0, sizeof(set), &set);
    int is_main_cpu = (cpu == probe_main_cpu);
    struct timespec next;
    clock_gettime(CLOCK_MONOTONIC, &next);
    long busy_since = 0, asleep_reported = 0, last_wd_report = 0;
    int samples = 0;
    for (;;) {
        next.tv_nsec += 1000000;
        if (next.tv_nsec >= 1000000000L) { next.tv_sec++; next.tv_nsec -= 1000000000L; }
        clock_nanosleep(CLOCK_MONOTONIC, TIMER_ABSTIME, &next, NULL);
        long now = probe_now_ns();
        long target = next.tv_sec * 1000000000L + next.tv_nsec;
        if (now - target > 1000000L && now - last_wd_report > 100000000L) {
            probe_log("watchdog cpu%d late: woke %.2f ms after its 1 ms tick%s", cpu, (now - target) / 1e6,
                      is_main_cpu ? " (MCU's CPU)" : " (other CPU)");
            last_wd_report = now;
        }
        if (!is_main_cpu) continue;
        long sleeping = probe_sleep_since_ns, armed = probe_armed_ns, prog = probe_progress_ns;
        if (sleeping) {
            if (armed > 1000000L && now - armed > 2000000L && asleep_reported != armed) {
                probe_log("main asleep in ppoll %.2f ms past its alarm (state=%c)", (now - armed) / 1e6, probe_state());
                asleep_reported = armed;
            }
            if (busy_since) {
                probe_log("main busy episode ended after %.2f ms", (sleeping - busy_since) / 1e6);
                busy_since = 0;
            }
        } else if (prog && now - prog > 5000000L) {
            if (!busy_since) { busy_since = prog; samples = 0; }
            if (samples < 6) {
                char sc[128];
                probe_read_proc("syscall", sc, sizeof(sc));
                probe_log("main busy %.2f ms: state=%c syscall=%s", (now - prog) / 1e6, probe_state(), sc);
                samples++;
            }
        } else if (busy_since) {
            probe_log("main busy episode ended after %.2f ms", (prog - busy_since) / 1e6);
            busy_since = 0;
        }
    }
    return NULL;
}

__attribute__((constructor(1002)))
static void probe_start(void) {
    if (!hw_is_mcu()) return;
    init_probe_funcs();
    probe_main_tid = (pid_t)syscall(SYS_gettid);
    int ncpu = (int)sysconf(_SC_NPROCESSORS_ONLN);
    if (ncpu < 1) ncpu = 1;
    // FAKE_HW_CPU=<n> pins the MCU to that CPU, otherwise to the one it starts on
    int cpu = getenv("FAKE_HW_CPU") ? atoi(getenv("FAKE_HW_CPU")) : sched_getcpu();
    if (cpu < 0 || cpu >= ncpu) cpu = 0;
    cpu_set_t set;
    CPU_ZERO(&set);
    CPU_SET(cpu, &set);
    if (sched_setaffinity(0, sizeof(set), &set) != 0) cpu = -1;
    probe_main_cpu = cpu;
    // a second watchdog on another CPU tells a system-wide stall (both late) from one that
    // only hits the MCU's CPU
    int other = (cpu + 1) % ncpu;
    // start the watchdogs with SIGALRM blocked so the alarm can never be delivered to them
    sigset_t alarm, old;
    sigemptyset(&alarm);
    sigaddset(&alarm, SIGALRM);
    pthread_sigmask(SIG_BLOCK, &alarm, &old);
    pthread_attr_t attr;
    pthread_attr_init(&attr);
    pthread_attr_setstacksize(&attr, 256 * 1024);  // small: the stack is locked by MCL_FUTURE
    pthread_t th;
    int ret = pthread_create(&th, &attr, probe_watchdog, (void *)(long)cpu);
    int ret2 = ncpu > 1 ? pthread_create(&th, &attr, probe_watchdog, (void *)(long)other) : -1;
    pthread_attr_destroy(&attr);
    pthread_sigmask(SIG_SETMASK, &old, NULL);
    probe_log("stall probe: main tid %d on cpu %d, watchdog on cpu %d %s, second watchdog on cpu %d %s",
              (int)probe_main_tid, cpu, cpu, ret == 0 ? "started" : strerror(ret),
              other, ret2 == 0 ? "started" : (ncpu > 1 ? strerror(ret2) : "skipped"));
}

// ─────────────────────────────────────────────────────────
// open()
// ─────────────────────────────────────────────────────────

int open(const char *path, int flags, ...) {
    init_real_funcs();
    mode_t mode = 0;
    if (flags & (O_CREAT | O_TMPFILE)) {
        va_list args;
        va_start(args, flags);
        mode = va_arg(args, mode_t);
        va_end(args);
    }

    // ADC: /sys/bus/iio/devices/iio:device0/in_voltageN_raw
    if (strstr(path, "in_voltage") && strstr(path, "_raw")) {
        int channel = 0;
        const char *p = strstr(path, "in_voltage");
        if (p) channel = atoi(p + strlen("in_voltage"));

        int fd = make_dummy_fd();
        if (fd < 0) return -1;
        FakeFd *f = alloc_fake_fd(fd, FD_ADC);
        if (!f) { real_close(fd); errno = ENOMEM; return -1; }
        f->channel = channel;
        if (hw_debug()) fprintf(stderr, "[fake_hw] open ADC channel %d -> fd %d\n", channel, fd);
        return fd;
    }

    // GPIO: /dev/gpiochipN
    if (strstr(path, "/dev/gpiochip")) {
        int chip = 0;
        sscanf(path, "/dev/gpiochip%d", &chip);
        int fd = make_dummy_fd();
        if (fd < 0) return -1;
        FakeFd *f = alloc_fake_fd(fd, FD_GPIO_CHIP);
        if (!f) { real_close(fd); errno = ENOMEM; return -1; }
        f->chip = chip;
        if (hw_debug()) fprintf(stderr, "[fake_hw] open gpiochip%d -> fd %d\n", chip, fd);
        return fd;
    }

    return real_open(path, flags, mode);
}

int open64(const char *path, int flags, ...) {
    mode_t mode = 0;
    if (flags & (O_CREAT | O_TMPFILE)) {
        va_list args;
        va_start(args, flags);
        mode = va_arg(args, mode_t);
        va_end(args);
    }
    return open(path, flags, mode);
}

// ─────────────────────────────────────────────────────────
// access() — Klipper checks if /dev/gpiochipN exists
// ─────────────────────────────────────────────────────────

int access(const char *path, int mode) {
    init_real_funcs();
    if (strstr(path, "/dev/gpiochip")) {
        if (hw_debug()) fprintf(stderr, "[fake_hw] access(%s) -> OK\n", path);
        return 0;
    }
    return real_access(path, mode);
}

// ─────────────────────────────────────────────────────────
// pread() — Read ADC values when Klipper tries to read from the in_voltageN_raw files
// ─────────────────────────────────────────────────────────

ssize_t pread(int fd, void *buf, size_t count, off_t offset) {
    init_real_funcs();
    FakeFd *f = find_fake_fd(fd);
    if (f && f->type == FD_ADC) {
        char key[32];
        snprintf(key, sizeof(key), "analog%d", f->channel);
        double t0 = hw_now_ms();
        int value = read_value(key, 0); // Default 0 für 12-bit ADC
        hw_report_slow("pread", key, t0);

        char tmp[32];
        int len = snprintf(tmp, sizeof(tmp), "%d\n", value);
        if (offset >= len) return 0;
        size_t n = (size_t)(len - offset) < count ? (size_t)(len - offset) : count;
        memcpy(buf, tmp + offset, n);
        if (hw_debug()) fprintf(stderr, "[fake_hw] pread ADC channel %d = %d\n", f->channel, value);
        return (ssize_t)n;
    }
    return real_pread(fd, buf, count, offset);
}

// ─────────────────────────────────────────────────────────
// ioctl() — GPIO v1 ABI (used by Klipper)
// ─────────────────────────────────────────────────────────

int ioctl(int fd, unsigned long request, ...) {
    init_real_funcs();
    va_list args;
    va_start(args, request);
    void *arg = va_arg(args, void*);
    va_end(args);

    FakeFd *f = find_fake_fd(fd);
    if (!f) return real_ioctl(fd, request, arg);

    // ── Chip-Info ────────────────────────────────────────
    if (request == GPIO_GET_CHIPINFO_IOCTL) {
        struct gpiochip_info *info = (struct gpiochip_info *)arg;
        memset(info, 0, sizeof(*info));
        snprintf(info->name,  sizeof(info->name),  "gpiochip%d", f->chip);
        snprintf(info->label, sizeof(info->label), "fake-gpio%d", f->chip);
        info->lines = 64;
        if (hw_debug()) fprintf(stderr, "[fake_hw] ioctl CHIPINFO chip%d\n", f->chip);
        return 0;
    }

    // ── Line-Info ────────────────────────────────────────
    if (request == GPIO_GET_LINEINFO_IOCTL) {
        struct gpioline_info *info = (struct gpioline_info *)arg;
        snprintf(info->name, sizeof(info->name), "gpio%u", info->line_offset);
        info->flags = 0;
        info->consumer[0] = '\0';
        return 0;
    }

    // ── Line handle request → return a new fd for the line ──
    if (request == GPIO_GET_LINEHANDLE_IOCTL) {
        struct gpiohandle_request *req = (struct gpiohandle_request *)arg;
        int line_fd = make_dummy_fd();
        if (line_fd < 0) { errno = ENOMEM; return -1; }
        FakeFd *lf = alloc_fake_fd(line_fd, FD_GPIO_LINE);
        if (!lf) { real_close(line_fd); errno = ENOMEM; return -1; }
        lf->chip      = f->chip;
        lf->num_lines = req->lines;
        for (int i = 0; i < (int)req->lines && i < GPIOHANDLES_MAX; i++)
            lf->line_offsets[i] = req->lineoffsets[i];
        req->fd = line_fd;
        if (hw_debug()) fprintf(stderr, "[fake_hw] ioctl GET_LINEHANDLE lines=%d -> fd %d\n",
                req->lines, line_fd);
        return 0;
    }

    // ── read GPIO ─────────────────────────────────────────
    if (request == GPIOHANDLE_GET_LINE_VALUES_IOCTL) {
        struct gpiohandle_data *data = (struct gpiohandle_data *)arg;
        memset(data, 0, sizeof(*data));
        for (int i = 0; i < f->num_lines && i < GPIOHANDLES_MAX; i++) {
            char key[32];
            snprintf(key, sizeof(key), "chip%d_gpio%d", f->chip, f->line_offsets[i]);
            double t0 = hw_now_ms();
            data->values[i] = read_value(key, 0) ? 1 : 0;
            hw_report_slow("GET", key, t0);
            if (hw_debug()) fprintf(stderr, "[fake_hw] ioctl GET %s = %d\n", key, data->values[i]);
        }
        return 0;
    }

    // ── write GPIO ───────────────────────────────────────
    if (request == GPIOHANDLE_SET_LINE_VALUES_IOCTL) {
        struct gpiohandle_data *data = (struct gpiohandle_data *)arg;
        for (int i = 0; i < f->num_lines && i < GPIOHANDLES_MAX; i++) {
            char key[32];
            snprintf(key, sizeof(key), "chip%d_gpio%d", f->chip, f->line_offsets[i]);
            if (hw_debug()) fprintf(stderr, "[fake_hw] ioctl SET %s = %d\n", key, data->values[i]);
            double t0 = hw_now_ms();
            write_value(key, data->values[i]);
            hw_report_slow("SET", key, t0);
        }
        return 0;
    }

    // Unsupported ioctls on fake fds
    errno = ENOTTY;
    return -1;
}

// ─────────────────────────────────────────────────────────
// close()
// ─────────────────────────────────────────────────────────

int close(int fd) {
    init_real_funcs();
    free_fake_fd(fd);
    return real_close(fd);
}