#!/bin/bash
# Zig 0.17 bootstrap chain from zb-built /data/zig17_2: compiler_rt + self -> zig17_3 -> self; compare (-j1 for determinism)
cd /data/zig17-src; ulimit -s unlimited
self() { "$1" build-exe -j1 -ofmt=c -lc -OReleaseSmall --name zig2 -femit-bin="$2" -target x86_64-linux --zig-lib-dir lib --dep build_options -Mroot=src/main.zig -Mbuild_options=config.zig; echo "self $1 EXIT $?"; }
[ -f /data/compiler_rt17.c ] || /data/zig17_2 build-obj -j1 -ofmt=c -OReleaseSmall --name compiler_rt -femit-bin=/data/compiler_rt17.c -target x86_64-linux --zig-lib-dir lib -Mroot=lib/compiler_rt.zig; echo "rt EXIT $?"
[ -f /data/zig17_2_self.c ] || self /data/zig17_2 /data/zig17_2_self.c
ZLIB=/data/zig17-src/lib RT=/data/compiler_rt17.c /data/zb/tools/stage.sh /data/zig17_2_self.c /data/zig17_3
self /data/zig17_3 /data/zig17_3_self.c
cmp /data/zig17_2_self.c /data/zig17_3_self.c && echo "ZIG17 zig2==zig3 IDENTICAL"
echo BOOT17DONE
