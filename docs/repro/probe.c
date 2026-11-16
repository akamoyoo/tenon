/* Minimal reproducer for the difftest mismatch seed 401, program 148, case 6 (MISMATCH-401-148.md).
   `probe` is the C the emitter prints for the Tenon function
       probe(x: f64) -> 0..=1   { if 1.0 <= x + x { res = 1 } else { res = 0 } }
   (Tenon term: fite (lit 1.0) (add (var 1) (var 1)) (assign 0 (lit 1)) (assign 0 (lit 0))),
   and `main` passes the input the way the difftest driver does: from a static union holding the bit
   pattern, in the same translation unit. x = 1e30; Tenon's evalFn gives 1.
   With -DRUNTIME the same input goes through a volatile, so the compiler cannot fold it. */
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>

int64_t probe(double x)
{
    int64_t res = 0;
    if (1.0 <= x + x) {
        res = 1;
    } else {
        res = 0;
    }
    return res;
}

static union { uint64_t u[1]; double d[1]; } fs = {{UINT64_C(0x46293e5939a08cea)}};   /* 1e30 */

int main(void)
{
#ifdef RUNTIME
    volatile double x = fs.d[0];
    printf("%" PRId64 "\n", probe(x));
#else
    printf("%" PRId64 "\n", probe(fs.d[0]));
#endif
    return 0;
}
