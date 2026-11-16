#!/usr/bin/env bash
# Shows the clang Float2Int miscompilation behind difftest mismatch 401/148 (MISMATCH-401-148.md).
cd "$(dirname "$0")"
LLVM=${LLVM:-$(dirname "$(command -v clang)")}
F="-std=c11 -ffp-contract=off -fno-fast-math"
echo "expected (Tenon evalFn): 1"
for cfg in "clang -O0:$LLVM/clang -O0" "clang -O1:$LLVM/clang -O1" "clang -O2:$LLVM/clang -O2" \
           "clang -O1 -fsanitize=address:$LLVM/clang -O1 -fsanitize=address" \
           "clang -O1 -fsanitize=pointer-overflow:$LLVM/clang -O1 -fsanitize=pointer-overflow" \
           "clang -O1 -fsanitize=object-size:$LLVM/clang -O1 -fsanitize=object-size" \
           "clang -O1 -fsanitize=undefined,address (the difftest build):$LLVM/clang -O1 -fsanitize=undefined,address -fno-sanitize-recover=all" \
           "clang -O2 -fsanitize=undefined:$LLVM/clang -O2 -fsanitize=undefined" \
           "clang -O1 -fsanitize=undefined, input through a volatile (-DRUNTIME):$LLVM/clang -O1 -fsanitize=undefined -DRUNTIME" \
           "gcc -O2:gcc -O2" "gcc -O1 -fsanitize=undefined,address:gcc -O1 -fsanitize=undefined,address"; do
  name=${cfg%%:*}; cmd=${cfg#*:}
  $cmd $F probe.c -o /tmp/tn_probe.bin 2>/dev/null && printf "%-75s %s\n" "$name" "$(/tmp/tn_probe.bin 2>&1 | head -1)"
done
rm -f /tmp/tn_probe.bin
echo "--- the pass in isolation: opt -passes=float2int float2int.ll (every function must return true)"
$LLVM/opt -passes=float2int -S float2int.ll | grep -E "^define|ret "
echo "--- reference: opt -passes=instcombine float2int.ll"
$LLVM/opt -passes=instcombine -S float2int.ll | grep -E "^define|ret " | paste - - | awk '{print $3, $NF}'
