#!/bin/sh
# full pipeline: zb -> qbe -> report
cd /data/zb && rm -f zb && make -s GC=1 2>&1 | grep -i '\berror\b'
cd /data/zig-src && /data/zb/zb src/main.zig -o /data/zig2.ssa --std-dir lib/std -Mbuild_options=config.zig -Maro=lib/compiler/aro/aro.zig 2>&1 | grep -v 'warning\|xgetbv' | head -5 | cut -c1-300
cd /data && /data/zb/qbe-1.2/qbe -o /data/zig2.s /data/zig2.ssa 2>&1 | head -5 && echo "qbe exit ok? $(ls -la /data/zig2.s | awk '{print $5}')"
