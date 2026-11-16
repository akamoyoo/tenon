/* Float benchmark driver. Every implementation lives in its own translation unit (no LTO) and is called
   through a volatile function pointer, so nothing is inlined into the timing loop.
   Method: per (workload, implementation, N): warm up for WARM_MS, then REPS timed runs of at least
   RUN_MS each (a run is as many whole calls as needed); report the minimum and the median in ns per
   element, and a checksum of the result (the bit pattern of a scalar result, the XOR of all output
   bit patterns for an array result), so that "same order of operations" is visible as "same bits".
   N = 10^7 doubles (80 MB per array: memory-bound) and N = 4096 (in the L1 cache: compute-bound). */
#define _POSIX_C_SOURCE 199309L
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

typedef int64_t (*sum_fn)(const double *, int64_t, double *, int64_t);
typedef int64_t (*dot_fn)(const double *, int64_t, const double *, int64_t, double *, int64_t);
typedef int64_t (*ew_fn)(const double *, int64_t, double, double *, int64_t);
typedef int64_t (*rw_fn)(const double *, int64_t, int64_t, double *, int64_t);
typedef int64_t (*clip_fn)(const double *, int64_t, double, double, double *, int64_t);
typedef int64_t (*wh_fn)(const int64_t *, int64_t, const double *, int64_t, const double *, int64_t, double *, int64_t);

#define DECL(t, n) extern int64_t n();
sum_fn gen_sum8_p, hand_sum8_p;
extern int64_t gen_sum8(const double *, int64_t, double *, int64_t), hand_sum8(const double *, int64_t, double *, int64_t),
               naive_sum_strict(const double *, int64_t, double *, int64_t), naive_sum_fast(const double *, int64_t, double *, int64_t);
extern int64_t gen_dot(const double *, int64_t, const double *, int64_t, double *, int64_t),
               hand_dot(const double *, int64_t, const double *, int64_t, double *, int64_t),
               naive_dot_strict(const double *, int64_t, const double *, int64_t, double *, int64_t),
               naive_dot_fast(const double *, int64_t, const double *, int64_t, double *, int64_t);
extern int64_t gen_ewma(const double *, int64_t, double, double *, int64_t), hand_ewma(const double *, int64_t, double, double *, int64_t);
extern int64_t gen_rmean(const double *, int64_t, int64_t, double *, int64_t), hand_rmean(const double *, int64_t, int64_t, double *, int64_t),
               gen_rstd(const double *, int64_t, int64_t, double *, int64_t),
               gen_rvar(const double *, int64_t, int64_t, double *, int64_t), gen_rvar_plain(const double *, int64_t, int64_t, double *, int64_t),
               gen_rvar_lazy(const double *, int64_t, int64_t, double *, int64_t), gen_rvar_mask(const double *, int64_t, int64_t, double *, int64_t);
extern int64_t gen_clip(const double *, int64_t, double, double, double *, int64_t), gen_clip_plain(const double *, int64_t, double, double, double *, int64_t),
               gen_clip_lazy(const double *, int64_t, double, double, double *, int64_t), gen_clip_mask(const double *, int64_t, double, double, double *, int64_t),
               hand_clip(const double *, int64_t, double, double, double *, int64_t);
extern int64_t gen_fwhere(const int64_t *, int64_t, const double *, int64_t, const double *, int64_t, double *, int64_t),
               gen_fwhere_plain(const int64_t *, int64_t, const double *, int64_t, const double *, int64_t, double *, int64_t),
               gen_fwhere_lazy(const int64_t *, int64_t, const double *, int64_t, const double *, int64_t, double *, int64_t),
               gen_fwhere_mask(const int64_t *, int64_t, const double *, int64_t, const double *, int64_t, double *, int64_t);

static int WARM_MS = 200, RUN_MS = 100, REPS = 15;
static uint64_t rng_state = 0x243F6A8885A308D3ull;
static uint64_t rng(void)
{
    uint64_t z = (rng_state += 0x9E3779B97F4A7C15ull);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ull;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBull;
    return z ^ (z >> 31);
}
static double now_ns(void)
{
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec * 1e9 + ts.tv_nsec;
}
static int cmp_d(const void *a, const void *b) { double x = *(const double *)a, y = *(const double *)b; return (x > y) - (x < y); }
static uint64_t bits1(double d) { uint64_t u; memcpy(&u, &d, 8); return u; }
static uint64_t fold(const double *p, int64_t n) { uint64_t h = 0; for (int64_t i = 0; i < n; i++) h = (h << 1 | h >> 63) ^ bits1(p[i]); return h; }

static double *X, *Y, *OUT; static int64_t *C; static double R1[1];
static int64_t N;

enum { K_SUM, K_DOT, K_EWMA, K_RW, K_CLIP, K_WHERE };
static void call(int kind, void *volatile fp)
{
    switch (kind) {
    case K_SUM: ((sum_fn)fp)(X, N, R1, 1); break;
    case K_DOT: ((dot_fn)fp)(X, N, Y, N, R1, 1); break;
    case K_EWMA: ((ew_fn)fp)(X, N, 0.05, OUT, N); break;
    case K_RW: ((rw_fn)fp)(X, N, 20, OUT, N); break;
    case K_CLIP: ((clip_fn)fp)(X, N, -0.5, 0.5, OUT, N); break;
    case K_WHERE: ((wh_fn)fp)(C, N, X, N, Y, N, OUT, N); break;
    }
}
static void bench(const char *work, const char *impl, int kind, void *fp)
{
    double t0 = now_ns();
    long calls = 0;
    do { call(kind, fp); calls++; } while (now_ns() - t0 < WARM_MS * 1e6);
    double per_call = (now_ns() - t0) / calls;
    long k = (long)(RUN_MS * 1e6 / per_call) + 1;
    double t[64];
    for (int r = 0; r < REPS; r++) {
        double a = now_ns();
        for (long j = 0; j < k; j++) call(kind, fp);
        t[r] = (now_ns() - a) / ((double)k * (double)N);
    }
    qsort(t, REPS, sizeof t[0], cmp_d);
    uint64_t cs = (kind == K_SUM || kind == K_DOT) ? bits1(R1[0]) : fold(OUT, N);
    printf("%-8s %-18s N=%-9" PRId64 " min %8.4f  median %8.4f ns/element   checksum %016" PRIx64 "\n", work, impl, N, t[0], t[REPS / 2], cs);
    fflush(stdout);
}

static void run_all(int64_t n)
{
    N = n;
    printf("-- N = %" PRId64 " --\n", N);
#define B(w, name, kind) bench(w, #name, kind, (void *)name)
    B("sum", gen_sum8, K_SUM); B("sum", hand_sum8, K_SUM); B("sum", naive_sum_strict, K_SUM); B("sum", naive_sum_fast, K_SUM);
    B("dot", gen_dot, K_DOT); B("dot", hand_dot, K_DOT); B("dot", naive_dot_strict, K_DOT); B("dot", naive_dot_fast, K_DOT);
    B("ewma", gen_ewma, K_EWMA); B("ewma", hand_ewma, K_EWMA);
    B("rmean", gen_rmean, K_RW); B("rmean", hand_rmean, K_RW);
    B("rstd", gen_rstd, K_RW);
    B("rvar", gen_rvar, K_RW); B("rvar", gen_rvar_plain, K_RW); B("rvar", gen_rvar_lazy, K_RW); B("rvar", gen_rvar_mask, K_RW);
    B("clip", gen_clip, K_CLIP); B("clip", gen_clip_plain, K_CLIP); B("clip", gen_clip_lazy, K_CLIP); B("clip", gen_clip_mask, K_CLIP);
    B("clip", hand_clip, K_CLIP);
    B("fwhere", gen_fwhere, K_WHERE); B("fwhere", gen_fwhere_plain, K_WHERE); B("fwhere", gen_fwhere_lazy, K_WHERE); B("fwhere", gen_fwhere_mask, K_WHERE);
}

int main(int argc, char **argv)
{
    int64_t big = 10000000;
    if (argc > 1) { big = 1000000; REPS = 5; WARM_MS = 50; RUN_MS = 30; }
    X = aligned_alloc(64, big * 8); Y = aligned_alloc(64, big * 8); OUT = aligned_alloc(64, big * 8); C = aligned_alloc(64, big * 8);
    for (int64_t i = 0; i < big; i++) {
        X[i] = (double)(int64_t)(rng() >> 11) / 9007199254740992.0 * 2.0 - 1.0;      /* uniform in [-1, 1) */
        Y[i] = (double)(int64_t)(rng() >> 11) / 9007199254740992.0 * 2.0 - 1.0;
        C[i] = (int64_t)(rng() & 1);
        OUT[i] = 0.0;
    }
    run_all(big);
    run_all(4096);
    return 0;
}
