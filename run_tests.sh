#!/bin/bash
# Compile each tests/*.zig with zb -> qbe -> cc, run, and compare stdout+exit code.
cd "$(dirname "$0")"
QBE=${QBE:-./qbe-1.2/qbe}
pass=0; fail=0
mkdir -p build; cc -O1 -c -o build/zbrt.o tools/zbrt.c
STD=${STD:-./zig-0.16.0/lib/std}
list="tests/*.zig"; [ -d "$STD" ] && list="$list tests/std/*.zig"
for t in $list; do
  b=build/$(basename $t .zig); extra=""
  case $t in tests/std/*) extra="--std-dir $STD";; esac
  if ! ./zb $t $extra -o $b.ssa 2> $b.err; then echo "FAIL (zb)   $t: $(head -1 $b.err)"; fail=$((fail+1)); continue; fi
  if ! $QBE -o $b.s $b.ssa 2> $b.err; then echo "FAIL (qbe)  $t: $(head -1 $b.err)"; fail=$((fail+1)); continue; fi
  if ! cc -o $b $b.s $b.ssa.asm.s build/zbrt.o -lm 2> $b.err; then echo "FAIL (link) $t: $(head -1 $b.err)"; fail=$((fail+1)); continue; fi
  out=$(timeout 5 ./$b 2>&1); code=$?
  got="$out
exit=$code"
  if [ "$got" == "$(cat ${t%.zig}.expected)" ]; then pass=$((pass+1)); else echo "FAIL (run)  $t"; diff <(echo "$got") ${t%.zig}.expected | head -10; fail=$((fail+1)); fi
done
echo "passed $pass, failed $fail"
