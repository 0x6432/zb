#!/bin/sh
# zb -> qbe -> cc -> run. Usage: tools/run.sh file.zig --std-dir /data/zb/zig-0.17.0/lib/std
f=$1; shift
/data/zb/zb "$f" -o /tmp/out.ssa "$@" && /data/zb/qbe-1.2/qbe -o /tmp/out.s /tmp/out.ssa && cc -o /tmp/out /tmp/out.s /tmp/out.ssa.asm.s /data/zb/tools/zbrt.c -lm && /tmp/out
