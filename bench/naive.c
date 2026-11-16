/* The baseline people compare a fixed-order sum against: one accumulator, left to right.
   This file is compiled twice: with the strict flags (SUFFIX = _strict; the compiler must keep the
   order, so the loop is a chain of dependent additions) and with -O2 -ffast-math (SUFFIX = _fast; the
   compiler may reorder and vectorise; NOT allowed for a Tenon kernel: the result depends on the
   compiler, its version and the target). */
#include <stdint.h>
#define CAT2(a, b) a##b
#define CAT(a, b) CAT2(a, b)

int64_t CAT(naive_sum, SUFFIX)(const double *restrict x, int64_t n, double *restrict out, int64_t out_len)
{
    (void)out_len;
    double s = 0.0;
    for (int64_t i = 0; i < n; i++) s += x[i];
    out[0] = s;
    return 0;
}

int64_t CAT(naive_dot, SUFFIX)(const double *restrict x, int64_t n, const double *restrict y, int64_t y_len, double *restrict out, int64_t out_len)
{
    (void)y_len; (void)out_len;
    double s = 0.0;
    for (int64_t i = 0; i < n; i++) s += x[i] * y[i];
    out[0] = s;
    return 0;
}
