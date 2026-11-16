#!/usr/bin/env bash
# Float benchmark: generated against hand-written C for ewma, sum8, dot, rolling_mean (and rolling_var,
# rolling_std, clip, fwhere in the four C forms of the float select) on 10^7 doubles and on 4096;
# sum8/dot against a left-to-right loop under the same strict flags and under -ffast-math; clang 21 and
# gcc, -O2 and -O2 -march=native; the assembly of sum8 and dot; then the Python binding against NumPy.
# Pinned to one core.     ./bench/run.sh        QUICK=1 ./bench/run.sh
set -eu
cd "$(dirname "$0")/.."
export PATH="$HOME/.elan/bin:$PATH"
LLVM=${LLVM:-$(dirname "$(command -v clang)")}
CPU=${CPU:-12}
OUT=build/bench
STRICT="-std=c11 -ffp-contract=off -fno-fast-math"
mkdir -p "$OUT/asm"
taskset -c 8-15 lake build benchgen > "$OUT/lake.log" 2>&1 || { grep -A8 "^error" "$OUT/lake.log"; exit 1; }
.lake/build/bin/benchgen "$OUT"
GEN="gen_ewma gen_sum8 gen_dot gen_rmean gen_rstd gen_rvar gen_rvar_plain gen_rvar_lazy gen_rvar_mask gen_clip gen_clip_plain gen_clip_lazy gen_clip_mask gen_fwhere gen_fwhere_plain gen_fwhere_lazy gen_fwhere_mask"
echo "machine: $(grep -m1 'model name' /proc/cpuinfo | cut -d: -f2 | sed 's/^ //'), $(uname -sr)"
echo "idle before the run (mpstat, cores 8-15): $(mpstat -P 8-15 1 1 2>/dev/null | awk '/Average/ && $2 ~ /[0-9]/ {printf "%s:%s%% ", $2, $NF}')"

clean_asm() { grep -vE '^\s*\.(file|text|globl|type|size|ident|section|p2align|cfi_|addrsig|addrsig_sym|Lfunc|L\$)|^\s*#|^\s*$|^\.Lfunc_end|^\s*\.addrsig' "$1" | sed -E 's/\s+#.*$//; s/\t/  /g'; }
one_fn() { awk -v f="$2:" '$1==f {on=1} on && /^[A-Za-z_][A-Za-z0-9_]*:/ && $1!=f {on=0} on && /^ *\.(align|long|string|quad)/ {on=0} on && !/^\.LF[BE]/' "$1" | grep -v endbr64; }

for comp in clang gcc; do
  if [ $comp = clang ]; then CC=$LLVM/clang; else CC=gcc; fi
  for arch in O2 O2-native; do
    if [ $arch = O2 ]; then OPT="-O2"; else OPT="-O2 -march=native"; fi
    T=$comp-$arch; B=$OUT/$T; mkdir -p "$B"
    objs=""
    for f in $GEN; do
      $CC $OPT $STRICT -c "$OUT/$f.c" -o "$B/$f.o"; $CC $OPT $STRICT -S "$OUT/$f.c" -o "$OUT/asm/$f.$T.s"; objs="$objs $B/$f.o"
    done
    $CC $OPT $STRICT -c bench/hand.c -o "$B/hand.o"; $CC $OPT $STRICT -S bench/hand.c -o "$OUT/asm/hand.$T.s"
    $CC $OPT $STRICT -DSUFFIX=_strict -c bench/naive.c -o "$B/naive_strict.o"; $CC $OPT $STRICT -DSUFFIX=_strict -S bench/naive.c -o "$OUT/asm/naive_strict.$T.s"
    # the forbidden baseline: -ffast-math
    $CC $OPT -std=c11 -ffast-math -DSUFFIX=_fast -c bench/naive.c -o "$B/naive_fast.o"; $CC $OPT -std=c11 -ffast-math -DSUFFIX=_fast -S bench/naive.c -o "$OUT/asm/naive_fast.$T.s"
    $CC -O2 -std=c11 -c bench/bench.c -o "$B/bench.o"
    $CC -O2 "$B/bench.o" $objs "$B/hand.o" "$B/naive_strict.o" "$B/naive_fast.o" -o "$B/bench" -lm
    echo "=== C benchmark, $comp $OPT $STRICT ($($CC --version | head -1)), pinned to cpu $CPU ==="
    echo "    (naive_*_fast is compiled with $OPT -ffast-math instead of the strict flags)"
    taskset -c "$CPU" "$B/bench" ${QUICK:+quick} | tee "$OUT/result.$T.txt"
  done
done

echo
echo "=== do the eight lanes become vector instructions? per function: instructions, packed-double instructions (addpd/mulpd/vaddpd/...), scalar ones (addsd/mulsd/...), fused multiply-adds ==="
for comp in clang gcc; do for arch in O2 O2-native; do
  T=$comp-$arch
  for f in $GEN hand naive_strict naive_fast; do clean_asm "$OUT/asm/$f.$T.s" > "$OUT/asm/$f.$T.clean"; done
  stat() {   # file function
    one_fn "$OUT/asm/$1.$T.clean" $2 > "$OUT/asm/$2.$T.fn"
    printf "%-16s %-18s instructions=%-4s packed_pd=%-3s (of which 256-bit ymm=%-3s) scalar_sd=%-3s fma=%-2s cond_jumps=%-2s blend_or_mask=%s\n" $T $2 \
      "$(grep -vc ':$' "$OUT/asm/$2.$T.fn")" "$(grep -cE '\s(v?(add|mul|sub|div|sqrt|max|min)pd)\s' "$OUT/asm/$2.$T.fn")" \
      "$(grep -E '\s(v(add|mul|sub|div|sqrt)pd)\s' "$OUT/asm/$2.$T.fn" | grep -c ymm)" \
      "$(grep -cE '\s(v?(add|mul|sub|div|sqrt)sd)\s' "$OUT/asm/$2.$T.fn")" "$(grep -cE 'vfn?m(add|sub)' "$OUT/asm/$2.$T.fn")" \
      "$(grep -cE '^\s*j[a-z]+\s' "$OUT/asm/$2.$T.fn" | awk -v u="$(grep -cE '^\s*jmp\s' "$OUT/asm/$2.$T.fn")" '{print $1-u}')" \
      "$(grep -cE 'blendv|vblend|andnp|vandnp|v?cmp[a-z]*[ps]d|vpblend|maskmov' "$OUT/asm/$2.$T.fn")"
  }
  stat gen_sum8 gen_sum8; stat hand hand_sum8; stat naive_strict naive_sum_strict; stat naive_fast naive_sum_fast
  stat gen_dot gen_dot; stat hand hand_dot; stat naive_strict naive_dot_strict; stat naive_fast naive_dot_fast
  stat gen_ewma gen_ewma; stat gen_rmean gen_rmean; stat gen_rstd gen_rstd
  for s in "" _plain _lazy _mask; do stat gen_rvar$s gen_rvar$s; done
  for s in "" _plain _lazy _mask; do stat gen_clip$s gen_clip$s; done
  stat hand hand_clip
  for s in "" _plain _lazy _mask; do stat gen_fwhere$s gen_fwhere$s; done
done; done
for T in clang-O2 clang-O2-native gcc-O2 gcc-O2-native; do
  for f in gen_sum8 gen_dot; do
    echo
    echo "=== assembly, $T: $f (whole function) ==="
    cat "$OUT/asm/$f.$T.fn"
  done
done
for T in clang-O2 clang-O2-native gcc-O2 gcc-O2-native; do
  echo
  echo "=== assembly, $T: gen_clip (selLe, default form) | gen_clip_lazy ==="
  pr -m -t -w 120 "$OUT/asm/gen_clip.$T.fn" "$OUT/asm/gen_clip_lazy.$T.fn"
  echo
  echo "=== assembly, $T: the main loop of naive_sum_fast (-ffast-math) ==="
  cat "$OUT/asm/naive_sum_fast.$T.fn"
done

echo
for T in clang clang-native gcc-native; do
  case $T in clang) CCp=$LLVM/clang; M="";; clang-native) CCp=$LLVM/clang; M=native;; gcc-native) CCp=gcc; M=native;; esac
  CC=$CCp MARCH=$M OUT=$OUT/py-$T ./py/build.sh | tail -1
  echo "=== Python binding against NumPy, library: $(cat $OUT/py-$T/BUILD_FLAGS.txt), pinned to cpu $CPU ==="
  TENON_BUILD=$OUT/py-$T PYTHONPATH=py OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 taskset -c "$CPU" python3 bench/bench_py.py ${QUICK:+quick} | tee "$OUT/result.py.$T.txt"
done
