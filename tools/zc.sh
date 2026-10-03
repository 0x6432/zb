#!/bin/sh
# Attempt to compile the Zig 0.16 compiler with zb. Usage: tools/zc.sh [nlines]
cd /data/zb && rm -f zb && make GC=1 2>&1 | grep -iE '\berror\b'
cd /data/zig-src && timeout 900 /data/zb/zb src/main.zig -o /tmp/zig2.ssa --std-dir lib/std \
  -Mbuild_options=config.zig -Maro=lib/compiler/aro/aro.zig 2>&1 | head -${1:-8} | cut -c1-300
