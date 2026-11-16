// Runs the generated par_sum on the data of examples/rust/parsum.rs and prints the bits of the result.
#define _POSIX_C_SOURCE 199309L
//   driver N REPEATS        (the number of threads comes from OMP_NUM_THREADS)
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>
int64_t par_sum(const double *x, int64_t x_len, double *parts, int64_t parts_len, double *out, int64_t out_len);
int main(int argc, char **argv) {
    int64_t n = argc > 1 ? atoll(argv[1]) : 1000000;
    int reps = argc > 2 ? atoi(argv[2]) : 1;
    double *x = malloc(n * sizeof *x);
    for (int64_t i = 0; i < n; i++) x[i] = sin((double)i * 0.7) * 1e8 + 1e-3 * (double)(i % 7);
    int64_t np = (n + 16383) / 16384;
    double *parts = malloc((np ? np : 1) * sizeof *parts), out[1];
    uint64_t first = 0; int distinct = 0; double best = 1e30;
    for (int r = 0; r < reps; r++) {
        struct timespec t0, t1; clock_gettime(CLOCK_MONOTONIC, &t0);
        par_sum(x, n, parts, np, out, 1);
        clock_gettime(CLOCK_MONOTONIC, &t1);
        double ms = (t1.tv_sec - t0.tv_sec) * 1e3 + (t1.tv_nsec - t0.tv_nsec) / 1e6;
        if (ms < best) best = ms;
        uint64_t b; memcpy(&b, out, 8);
        if (r == 0) first = b; else if (b != first) distinct++;
    }
    printf("bits %016llx  runs %d  runs differing from the first %d  best %.2f ms\n",
           (unsigned long long)first, reps, distinct, best);
    return 0;
}
