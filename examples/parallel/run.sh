#!/usr/bin/env bash
# Generates the C for examples/par_sum.tn, builds it with OpenMP, and runs it with several thread counts:
# the bits of the result must be the same for every thread count and every run, and equal to the value
# the Lean semantics gives (checked for small sizes by check.c against the numbers in check.expected).
set -eu
cd "$(dirname "$0")"
CC=${CC:-gcc}
../../tenon emit ../par_sum.tn 2>/dev/null > par_sum.c
$CC -O2 -std=c11 -ffp-contract=off -fno-fast-math -fopenmp par_sum.c driver.c -o run -lm
$CC -O2 -std=c11 -ffp-contract=off -fno-fast-math -fopenmp par_sum.c check.c -o check -lm
OMP_NUM_THREADS=4 ./check > check.out
diff check.expected check.out && echo "C agrees with the Lean semantics on 0, 1, 16384 and 17000 elements"
first=""
for t in ${THREADS:-1 2 4 8 16}; do
  line=$(OMP_NUM_THREADS=$t ./run ${N:-1000000} ${REPS:-200})
  echo "threads $t: $line"
  bits=${line%%  *}
  [ -z "$first" ] && first=$bits
  [ "$bits" = "$first" ] || { echo "DIFFERENT RESULT"; exit 1; }
  case "$line" in *"differing from the first 0 "*) ;; *) echo "DIFFERENT RESULT WITHIN ONE THREAD COUNT"; exit 1;; esac
done
echo "same bits for every thread count"
