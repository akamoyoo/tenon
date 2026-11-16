#!/usr/bin/env bash
# Differential test: Tenon reference semantics (evalFn, compiled Lean) against the emitted C.
#   ./difftest/run.sh                 default size
#   SEEDS="1 2 3" NPROGS=500 NINPUTS=16 ./difftest/run.sh
# Run from anywhere; everything is written under build/difftest/.
set -u
cd "$(dirname "$0")/.."
export PATH="$HOME/.elan/bin:$PATH"
CLANG=${CLANG:-clang}
GCC=${GCC:-gcc}
SEEDS=${SEEDS:-"1 2 3 4 5 6 7 8"}
NPROGS=${NPROGS:-500}
NINPUTS=${NINPUTS:-16}
CPUS=${CPUS:-0-$(( $(nproc) - 1 ))}
OUT=build/difftest
# The flags the float guarantee needs (README.md, "Compiler flags"): no contraction, no fast-math.
W="-std=c11 -w -ffp-contract=off -fno-fast-math"
BUILDS="clang-O0 clang-O2 gcc-O0 gcc-O2 clang-ubsan clang-O2-native gcc-O2-native"

lake build difftest > build-difftest.log 2>&1 || { grep -E "^error" build-difftest.log; echo "lake build failed"; exit 1; }
grep -E "Build completed" build-difftest.log; rm -f build-difftest.log
rm -rf "$OUT"; mkdir -p "$OUT"
# The generator runs the reference evaluator on every input. Loop bounds in generated programs are
# small by construction (forN <= 12, forE bounds clamped to <= 12 or len <= 24, loopB/loopE proof
# bounds <= 64 or 1100, nesting depth <= 2), but an unbounded run must never be left behind: every
# invocation has a time limit.
DT="timeout 900 .lake/build/bin/difftest"

# compile one batch directory with every configuration and run it
build_and_run() {
  d=$1
  for cfg in "clang-O0:$CLANG -O0" "clang-O2:$CLANG -O2" "gcc-O0:$GCC -O0" "gcc-O2:$GCC -O2" \
             "clang-ubsan:$CLANG -O1 -fsanitize=undefined,address -fno-sanitize-recover=all" \
             "clang-O2-native:$CLANG -O2 -march=native" "gcc-O2-native:$GCC -O2 -march=native"; do
    name=${cfg%%:*}; cmd=${cfg#*:}
    (
    if ! $cmd $W "$d/batch.c" -o "$d/$name.bin" -lm 2> "$d/$name.cc.log"; then
      echo "COMPILE FAILED $d $name"; head -5 "$d/$name.cc.log"; : > "$d/$name.out"; exit 0
    fi
    timeout 600 "$d/$name.bin" > "$d/$name.out" 2> "$d/$name.err" || echo "RUN FAILED (exit $?) $d $name: $(head -3 "$d/$name.err")"
    ) &
  done
  wait
}
compare() {
  d=$1
  a=""; for b in $BUILDS; do a="$a $b=$d/$b.out"; done
  python3 difftest/compare.py "$d/expected.txt" $a
}
export -f build_and_run; export CLANG GCC W

status=0
echo "== 1. hand-written programs (Examples.lean), $((NINPUTS * 25)) random inputs each =="
$DT suite "$OUT/suite" 1 $((NINPUTS * 25)) | tee "$OUT/suite.gen.log"
taskset -c $CPUS bash -c "build_and_run $OUT/suite"
compare "$OUT/suite" || status=1

echo "== 1b. the same hand-written programs with the other three C forms of sel (no hint, lazy ?:, bit mask) =="
for form in plain lazy mask; do
  $DT suite "$OUT/suite-$form" 1 $((NINPUTS * 25)) none $form > /dev/null
  cmp -s "$OUT/suite-$form/expected.txt" "$OUT/suite/expected.txt" || { echo "FAIL: expected results differ"; status=1; }
  taskset -c $CPUS bash -c "build_and_run $OUT/suite-$form"
  echo "-- sel form $form: $(grep -c 'tn_sel\|tn_fsel\|?' "$OUT/suite-$form/batch.c") lines of C use the form"
  compare "$OUT/suite-$form" || status=1
done

echo "== 2. random programs: seeds [$SEEDS], $NPROGS programs per seed, $NINPUTS inputs per program =="
for s in $SEEDS; do
  $DT random "$OUT/r$s" "$s" "$NPROGS" "$NINPUTS" > "$OUT/r$s.gen.log" || status=1
done
printf '%s\n' $SEEDS | taskset -c $CPUS xargs -P 8 -I{} bash -c "build_and_run $OUT/r{}"
for s in $SEEDS; do
  echo "-- seed $s: $(tr '\n' ' ' < "$OUT/r$s.gen.log")"
  compare "$OUT/r$s" || status=1
done
first=${SEEDS%% *}
echo "== 2b. random programs of seed $first with the other three C forms of sel =="
for form in plain lazy mask; do
  $DT random "$OUT/r$first-$form" "$first" "$NPROGS" "$NINPUTS" none $form > /dev/null
  cmp -s "$OUT/r$first-$form/expected.txt" "$OUT/r$first/expected.txt" || { echo "FAIL: expected results differ"; status=1; }
done
printf '%s\n' plain lazy mask | taskset -c $CPUS xargs -P 3 -I{} bash -c "build_and_run $OUT/r$first-{}"
for form in plain lazy mask; do echo "-- sel form $form"; compare "$OUT/r$first-$form" || status=1; done

echo "== 3. self-tests of the harness =="
# 3a. known-stuck inputs must be `none` in the expected file and must not be called from the C driver:
#     the four stuck inputs of k3_lower_bound (wrong length; n = 9; p out of range; element out of
#     range), of rolling_sum (out shorter than x; w = 0; w too large; element out of range) and of
#     prefix_sum, and every input of k3_alias_bad (its only call is not exclusive).
pid() { grep -E "^suite-program [0-9]+ .* $1 \(" "$OUT/suite.gen.log" | awk '{print $2}'; }
for name in k3_lower_bound rolling_sum prefix_sum ewma dot; do
  p=$(pid $name)
  n_none=$(grep -cE "^$p [0123] 0 none\$" "$OUT/suite/expected.txt")
  n_call=$(grep -cE "printf\(\"$p [0123] " "$OUT/suite/batch.c")
  if [ "$n_none" = 4 ] && [ "$n_call" = 0 ]; then echo "3a PASS: the 4 known-stuck inputs of $name are none, 0 of them are called from C"
  else echo "3a FAIL: $name none=$n_none called=$n_call"; status=1; fi
done
p=$(pid k3_alias_bad)
n_some=$(grep -cE "^$p [0-9]+ 0 some" "$OUT/suite/expected.txt")
n_none=$(grep -cE "^$p [0-9]+ 0 none\$" "$OUT/suite/expected.txt")
n_call=$(grep -cE "printf\(\"$p [0-9]+ " "$OUT/suite/batch.c")
if [ "$n_some" = 0 ] && [ "$n_none" -gt 0 ] && [ "$n_call" = 0 ]; then echo "3a PASS: k3_alias_bad (non-exclusive call): $n_none inputs, all none, 0 called from C"
else echo "3a FAIL: k3_alias_bad some=$n_some none=$n_none called=$n_call"; status=1; fi
p=$(pid k3_alias_branch)
n_some=$(grep -cE "^$p [0-9]+ 0 some" "$OUT/suite/expected.txt")
n_none=$(grep -cE "^$p [0-9]+ 0 none\$" "$OUT/suite/expected.txt")
if [ "$n_some" -gt 0 ] && [ "$n_none" -gt 0 ]; then echo "3a PASS: k3_alias_branch (non-exclusive call on one branch): $n_some inputs compared, $n_none none"
else echo "3a FAIL: k3_alias_branch some=$n_some none=$n_none"; status=1; fi
# 3b. a C result for a `none` case must be reported as an error, not counted as a pass.
p=$(pid k3_lower_bound)
( cat "$OUT/suite/clang-O2.out"; echo "$p 0 3 1 3 5 7 9 11 13 15" ) > "$OUT/suite/fake.out"
if python3 difftest/compare.py "$OUT/suite/expected.txt" fake="$OUT/suite/fake.out" > "$OUT/suite/fake.log"; then
  echo "3b FAIL: a result for a none case was accepted"; status=1
else echo "3b PASS: $(grep -c ERROR "$OUT/suite/fake.log") error reported for a C result on a none input"; fi
# 3c. a wrong final value of an inout parameter (the result being right) must be a mismatch.
p=$(pid k3_ring_push)
awk -v p="$p" 'BEGIN{done=0} { if (!done && $1==p) { $NF=$NF+1; done=1 } print }' "$OUT/suite/clang-O2.out" > "$OUT/suite/fake2.out"
if python3 difftest/compare.py "$OUT/suite/expected.txt" fake="$OUT/suite/fake2.out" > "$OUT/suite/fake2.log"; then
  echo "3c FAIL: a wrong final parameter value was accepted"; status=1
else echo "3c PASS: $(grep -o 'mismatches=[0-9]*' "$OUT/suite/fake2.log") for one altered final value of an inout parameter ($(grep -o '(final parameter values)' "$OUT/suite/fake2.log" | head -1))"; fi
# 3c2. a write one past the end of a slice (the canary after every array) must be an error.
sed '0,/^[0-9]/s/^\([0-9].*\)$/\1 OVERRUN/' "$OUT/suite/clang-O2.out" > "$OUT/suite/fake3.out"
if python3 difftest/compare.py "$OUT/suite/expected.txt" fake="$OUT/suite/fake3.out" > "$OUT/suite/fake3.log"; then
  echo "3c2 FAIL: an OVERRUN marker was accepted"; status=1
else echo "3c2 PASS: an OVERRUN marker in a result line is reported ($(grep -o ' errors=[0-9]*' "$OUT/suite/fake3.log" | tr -d ' '))"; fi
# 3d. deliberate emitter breakages (Emit.lean, `Sabotage`): the same programs and inputs are emitted
#     by a broken emitter; the comparison must report mismatches for each.
#     (A broken program may crash or loop; it runs under a time limit and missing results count.)
sabotage() {
  mode=$1; OUT=$2; first=$3
  m="$OUT/sab-$mode"; mkdir -p "$m"
  $DT suite "$m/suite" 1 $((NINPUTS * 25)) $mode > /dev/null
  $DT random "$m/r" "$first" "$NPROGS" "$NINPUTS" $mode > /dev/null
  for d in suite r; do
    if [ $d = suite ]; then ref="$OUT/suite"; else ref="$OUT/r$first"; fi
    cmp -s "$m/$d/expected.txt" "$ref/expected.txt" || echo "3d FAIL: expected results changed under sabotage"
    changed=$(diff "$ref/batch.c" "$m/$d/batch.c" | grep -c '^[<>]')
    $CLANG -O2 $W "$m/$d/batch.c" -o "$m/$d/m.bin" -lm && DT_LINEBUF=1 timeout 20 "$m/$d/m.bin" 2>/dev/null | head -c 50000000 > "$m/$d/m.out"
    if python3 difftest/compare.py "$m/$d/expected.txt" broken="$m/$d/m.out" > "$m/$d/m.log"; then
      echo "3d MISS: breakage '$mode' ($changed differing lines of C) NOT detected in $d"
    else echo "3d PASS: breakage '$mode' ($changed differing lines of C) detected in $d: $(grep -o 'mismatches=[0-9]* ([a-z0-9= ]*)' "$m/$d/m.log") $(grep -o 'float_values_wrong=[0-9]*' "$m/$d/m.log")"; fi
  done
}
export -f sabotage; export DT NINPUTS NPROGS
SABS="lt noCopy counter noWriteBack inoutCopy loopBOnce loopBShort selSwap selTruthy ltAsLe eqAsLe leAsLt lenOff forEReeval forEShort sliceNoCopy fma reassoc selLeNaN fleAsLt fselSwap ofIntF32 sqrtF32 absDrop negSub loopEEval"
printf '%s\n' $SABS |
  taskset -c $CPUS xargs -P 8 -I{} bash -c "sabotage {} $OUT $first > $OUT/sab-{}.log 2>&1"
for mode in $SABS; do
  # required: detected in the hand-written suite or in the random programs; a MISS in one of the two
  # is printed and counted below, it does not hide
  cat "$OUT/sab-$mode.log"; grep -q "^3d PASS" "$OUT/sab-$mode.log" || status=1
  grep -q "FAIL" "$OUT/sab-$mode.log" && status=1
done

# 3e. the right C compiled with the wrong flags. The emitted file carries `#pragma STDC FP_CONTRACT OFF`
#     and an #error for fast-math; this measures what each of them is worth. FMA instructions exist
#     only with -mfma (or -march=native on this CPU), so every line has it.
echo "3d summary: $(cat $OUT/sab-*.log | grep -c '^3d PASS') detections, $(cat $OUT/sab-*.log | grep -c '^3d MISS') misses: $(cat $OUT/sab-*.log | grep '^3d MISS' | sed -E "s/.*breakage '([A-Za-z0-9]*)'.* in ([a-z]*)\$/\1(\2)/" | tr '\n' ' ')"
echo "== 3e. compiler flags: the emitter's C, unchanged, built in ways the float guarantee forbids =="
flagtest() {
  name=$1; expect=$2; shift 2
  for d in suite "r$first"; do
    src="$OUT/$d/batch.c"; [ "$name" = "clang-fma-nopragma" -o "$name" = "gcc-gnu11-nopragma" ] && { grep -v 'pragma STDC FP_CONTRACT' "$OUT/$d/batch.c" > "$OUT/$d/nopragma.c"; src="$OUT/$d/nopragma.c"; }
    if ! "$@" -w "$src" -o "$OUT/$d/$name.bin" -lm 2> "$OUT/$d/$name.cc.log"; then
      r="REFUSED AT COMPILE TIME ($(grep -m1 -o 'error: .*' "$OUT/$d/$name.cc.log" | cut -c1-90))"; got=refused
    else
      timeout 300 "$OUT/$d/$name.bin" > "$OUT/$d/$name.out" 2>/dev/null
      if python3 difftest/compare.py "$OUT/$d/expected.txt" x="$OUT/$d/$name.out" > "$OUT/$d/$name.log"; then r="no mismatch"; got=same
      else r="DETECTED: $(grep -o 'mismatches=[0-9]*' "$OUT/$d/$name.log") $(grep -o 'float_values_wrong=[0-9]*' "$OUT/$d/$name.log")"; got=differs; fi
    fi
    if [ "$expect" = any ] || [ "$expect" = "$got" ]; then v="as expected"; else v="UNEXPECTED (expected: $expect)"; flagstatus=1; fi
    echo "3e $name [$*] on $d: $r -- $v"
  done
}
flagstatus=0
export -f flagtest; export OUT first flagstatus
ft() { ( flagtest "$@" > "$OUT/flag-$1.log" 2>&1; ) & }
ft clang-fma-fast     differs $CLANG -O2 -std=c11 -mfma -ffp-contract=fast
ft gcc-fma-fast       differs $GCC   -O2 -std=c11 -mfma -ffp-contract=fast
ft gcc-gnu11-default  differs $GCC   -O2 -std=gnu11 -march=native
ft gcc-c11-default    same    $GCC   -O2 -std=c11 -march=native
ft clang-fma-default  same    $CLANG -O2 -std=c11 -march=native
ft clang-fma-nopragma differs $CLANG -O2 -std=c11 -march=native
ft clang-fastmath     refused $CLANG -O2 -std=c11 -ffast-math
ft gcc-fastmath       refused $GCC   -O2 -std=c11 -ffast-math
ft gcc-assoc          any     $GCC   -O2 -std=c11 -fassociative-math -fno-signed-zeros -fno-trapping-math
ft gcc-no-signed-zero any     $GCC   -O2 -std=c11 -ffp-contract=off -fno-signed-zeros
ft gcc-x87            any     $GCC   -O2 -std=c11 -ffp-contract=off -mfpmath=387
wait
cat "$OUT"/flag-*.log > "$OUT/flags.log"
cat "$OUT/flags.log"; grep -q UNEXPECTED "$OUT/flags.log" && status=1

echo "== total =="
python3 - "$OUT" <<'PY'
import sys, glob, re
out = sys.argv[1]
progs = some = none = pw = vals = fl = 0
for f in [out + '/suite/expected.txt'] + sorted(glob.glob(out + '/r[0-9]/expected.txt') + glob.glob(out + '/r[0-9][0-9]/expected.txt')):
    ps, pn = set(), set()
    for line in open(f):
        t = line.split()
        if not t or t[0] == '#': continue
        if t[3] == 'some': some += 1; ps.add(t[0]); vals += len(t) - 4; fl += sum(1 for x in t[4:] if x.startswith('f:'))
        else: none += 1
        pn.add(t[0])
    progs += len(pn); pw += len(ps)
tot = {}
for f in [out + '/suite.gen.log'] + sorted(glob.glob(out + '/r[0-9].gen.log') + glob.glob(out + '/r[0-9][0-9].gen.log')):
    for k, v in re.findall(r'(\w+)=(\d+)', open(f).read()):
        if k not in ('some', 'none'): tot[k] = tot.get(k, 0) + int(v)
print(f"programs={progs} programs_with_comparable_input={pw} inputs_compared(evalFn=some)={some} "
      f"inputs_skipped(evalFn=none)={none} values_compared={vals} (of which doubles, compared on the bit pattern: {fl}); each compared input was run in 7 C builds (the suite and the first seed in 28: four C forms of sel)")
print("sums over all batches: " + " ".join(f"{k}={v}" for k, v in tot.items()))
PY
[ $status = 0 ] && echo "RESULT: no mismatch" || echo "RESULT: MISMATCH OR ERROR (see above)"
exit $status
