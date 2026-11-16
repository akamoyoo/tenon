#define _POSIX_C_SOURCE 199309L
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int64_t par_sum(const double *x, int64_t x_len, double *parts, int64_t parts_len, double *out, int64_t out_len);
int main(void) {
    int64_t ns[] = {0, 1, 16384, 17000};
    for (int k = 0; k < 4; k++) {
        int64_t n = ns[k], np = (n + 16383) / 16384;
        double *x = malloc((n ? n : 1) * sizeof *x), *parts = calloc(np ? np : 1, sizeof *parts), out[1] = {0.0};
        for (int64_t i = 0; i < n; i++) x[i] = (double)((i * 7919) % 10007) * 0.37 - 1234.5;
        par_sum(x, n, parts, np ? np : 1, out, 1);
        uint64_t b; memcpy(&b, out, 8);
        printf("%lld %llu\n", (long long)n, (unsigned long long)b);
    }
}
