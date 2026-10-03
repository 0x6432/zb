#!/bin/bash
# zb -> Zig 0.17.0 compiler (/data/zig17_2) via QBE. Source: /data/zig17-src (config.zig = tools/config17.zig)
set -e
cd /data/zig17-src && /data/zb/zb src/main.zig -o /data/zig17_2.ssa --std-dir lib/std -Mbuild_options=config.zig 2>&1 | grep -v 'note:' | head -5
cd /data && /data/zb/qbe-1.2/qbe -o zig17_2.s zig17_2.ssa
cc -c -o zig17_2.o zig17_2.s 2>&1 | grep -v 'Warning\|Assembler messages' | head -5 || true
cc -O1 -c -o zbrt.o /data/zb/tools/zbrt.c
cc -o zig17_2 zig17_2.o zig17_2.ssa.asm.s zbrt.o -lm -pthread -Wl,-z,stack-size=0x10000000
ls -la /data/zig17_2
