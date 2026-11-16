/* Hand-written C for the float benchmark: what one would write without the generator, same algorithms
   and the same order of floating-point operations as the Tenon kernels. Compiled with the same strict
   flags as the generated code. */
#include <stdint.h>

int64_t hand_ewma(const double *restrict x, int64_t n, double alpha, double *restrict out, int64_t out_len)
{
    (void)out_len;
    double prev = 0.0;
    for (int64_t i = 0; i < n; i++) {
        prev = alpha * x[i] + (1.0 - alpha) * prev;
        out[i] = prev;
    }
    return 0;
}

int64_t hand_sum8(const double *restrict x, int64_t n, double *restrict out, int64_t out_len)
{
    (void)out_len;
    double a[8] = {0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0};
    int64_t i = 0;
    for (; i + 8 <= n; i += 8)
        for (int k = 0; k < 8; k++) a[k] += x[i + k];
    for (; i < n; i++) a[0] += x[i];
    out[0] = ((a[0] + a[1]) + (a[2] + a[3])) + ((a[4] + a[5]) + (a[6] + a[7]));
    return 0;
}

int64_t hand_dot(const double *restrict x, int64_t n, const double *restrict y, int64_t y_len, double *restrict out, int64_t out_len)
{
    (void)y_len; (void)out_len;
    double a[8] = {0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0};
    int64_t i = 0;
    for (; i + 8 <= n; i += 8)
        for (int k = 0; k < 8; k++) a[k] += x[i + k] * y[i + k];
    for (; i < n; i++) a[0] += x[i] * y[i];
    out[0] = ((a[0] + a[1]) + (a[2] + a[3])) + ((a[4] + a[5]) + (a[6] + a[7]));
    return 0;
}

int64_t hand_rmean(const double *restrict x, int64_t n, int64_t w, double *restrict out, int64_t out_len)
{
    (void)out_len;
    double acc = 0.0;
    int64_t m = w < n ? w : n;
    for (int64_t i = 0; i < m; i++) {
        acc += x[i];
        out[i] = acc / (double)(i + 1);
    }
    for (int64_t i = m; i < n; i++) {
        acc = acc + x[i] - x[i - m];
        out[i] = acc / (double)m;
    }
    return 0;
}

/* clip as a C programmer writes it */
int64_t hand_clip(const double *restrict x, int64_t n, double lo, double hi, double *restrict out, int64_t out_len)
{
    (void)out_len;
    for (int64_t i = 0; i < n; i++) {
        double v = x[i];
        out[i] = v <= lo ? lo : (hi <= v ? hi : v);
    }
    return 0;
}
