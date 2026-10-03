#!/bin/bash
# full pipeline -> /data/zig2 ; extra env passed through (e.g. ZB_TRAPLOC=1)
cd /data/zb && rm -f zb && make -s GC=1 2>&1 | grep -i '\berror\b'
cd /data/zig-src && /data/zb/zb src/main.zig -o /data/zig2.ssa --std-dir lib/std -Mbuild_options=config.zig -Maro=lib/compiler/aro/aro.zig 2>&1 | grep -v 'warning\|xgetbv' | head -5 | cut -c1-300
cd /data && /data/zb/qbe-1.2/qbe -o zig2.s zig2.ssa 2>&1 | head -5
cc -c -o zig2.o zig2.s 2>&1 | grep -v 'Warning\|Assembler messages' | head -5
cc -O1 -fno-omit-frame-pointer -c -o zbrt.o /data/zb/tools/zbrt.c; cc -o zig2 zig2.o zbrt.o -lm -pthread -Wl,-z,stack-size=0x10000000 2>&1 | head -5
ls -la /data/zig2
