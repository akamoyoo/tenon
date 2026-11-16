#!/usr/bin/env bash
# Builds the shared library the Python binding loads:  py/build/libtenon_kernels.so (+ tenon_kernels.c, .json)
#   ./py/build.sh                  clang 21 -O2
#   CC=gcc ./py/build.sh           gcc
#   MARCH=native OUT=py/build-native ./py/build.sh     with -march=native (AVX2/FMA available to the compiler)
# The float guarantee needs -ffp-contract=off and no fast-math option (README.md, "Compiler flags").
set -eu
cd "$(dirname "$0")/.."
export PATH="$HOME/.elan/bin:$PATH"
CC=${CC:-clang}
OUT=${OUT:-py/build}
MARCH=${MARCH:-}
lake build pygen > "$OUT.lake.log" 2>&1 || { grep -E "^error" -A8 "$OUT.lake.log"; exit 1; }
rm -f "$OUT.lake.log"
.lake/build/bin/pygen "$OUT"
FLAGS="-O2 -std=c11 -ffp-contract=off -fno-fast-math ${MARCH:+-march=$MARCH}"
$CC $FLAGS -fPIC -shared -Wall -Wno-unused-parameter -Wno-unused-function -Wno-unknown-pragmas "$OUT/tenon_kernels.c" -o "$OUT/libtenon_kernels.so" -lm
echo "$CC $FLAGS" > "$OUT/BUILD_FLAGS.txt"
echo "built $OUT/libtenon_kernels.so with $($CC --version | head -1), flags: $FLAGS"
