#!/bin/bash
# zig2 compiles the whole compiler to C (bootstrap step) -> /data/zig2_self.c ; log /tmp/self.log
cd /data/zig-src && ulimit -s unlimited; s=$(date +%s)
/data/zig2 build-exe -j1 -ofmt=c -lc -OReleaseSmall --name zig2 -femit-bin=/data/zig2_self.c -target x86_64-linux --zig-lib-dir lib --dep build_options --dep aro -Mroot=src/main.zig -Mbuild_options=config.zig -Maro=lib/compiler/aro/aro.zig
echo "EXIT $? after $(( $(date +%s) - s ))s"
