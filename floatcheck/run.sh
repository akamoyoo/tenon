#!/usr/bin/env bash
# Lean `Float` against the generated C, operation by operation, on the bit patterns.
#   ./floatcheck/run.sh           writes build/floatcheck/, prints the comparison
set -u
cd "$(dirname "$0")/.."
export PATH="$HOME/.elan/bin:$PATH"
CLANG=${CLANG:-clang}
GCC=${GCC:-gcc}
N=${N:-30000}
OUT=build/floatcheck
STRICT="-std=c11 -w -ffp-contract=off -fno-fast-math"
lake build fpcheck 2>&1 | grep -E "^error|Build completed" || exit 1
rm -rf "$OUT"; mkdir -p "$OUT/compiled" "$OUT/interp"
status=0
echo "== compiled Lean =="
.lake/build/bin/fpcheck "$OUT/compiled" $N || status=1
echo "== interpreted Lean (lean --run) =="
lake env lean --run floatcheck/FloatCheck.lean "$OUT/interp" $N || status=1
if cmp -s "$OUT/compiled/expected.txt" "$OUT/interp/expected.txt"; then echo "compiled and interpreted Lean: identical results ($(wc -l < "$OUT/compiled/expected.txt") lines)"
else echo "compiled and interpreted Lean DIFFER: $(diff "$OUT/compiled/expected.txt" "$OUT/interp/expected.txt" | grep -c '^<') lines"; status=1; fi
d="$OUT/compiled"
args=""
for cfg in "clang-O0:$CLANG -O0" "clang-O2:$CLANG -O2" "clang-O2-native:$CLANG -O2 -march=native" \
           "gcc-O0:$GCC -O0" "gcc-O2:$GCC -O2" "gcc-O2-native:$GCC -O2 -march=native" "gcc-O3-native:$GCC -O3 -march=native"; do
  name=${cfg%%:*}; cmd=${cfg#*:}
  $cmd $STRICT "$d/ops.c" -o "$d/$name.bin" -lm || { echo "COMPILE FAILED $name"; status=1; continue; }
  "$d/$name.bin" > "$d/$name.out"
  args="$args $name=$d/$name.out"
done
echo "== C built with: <compiler> $STRICT =="
python3 floatcheck/compare_ops.py "$d/inputs.txt" "$d/expected.txt" $args || status=1
echo "== for contrast: the same C with contraction allowed (-mfma -ffp-contract=fast); 'muladd' must differ =="
for cfg in "clang-fma-fast:$CLANG -O2 -mfma -ffp-contract=fast" "gcc-fma-fast:$GCC -O2 -mfma -ffp-contract=fast"; do
  name=${cfg%%:*}; cmd=${cfg#*:}
  $cmd -std=c11 -w "$d/ops.c" -o "$d/$name.bin" -lm && "$d/$name.bin" > "$d/$name.out"
  python3 floatcheck/compare_ops.py "$d/inputs.txt" "$d/expected.txt" $name=$d/$name.out | grep -E "MISMATCH|muladd"
done
[ $status = 0 ] && echo "RESULT: Lean Float and the generated C agree on every non-NaN result" || echo "RESULT: DISAGREEMENT (see above)"
exit $status
