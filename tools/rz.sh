#!/bin/bash
# run zig2 on hello.zig -> C
cd /data/zig-src && ulimit -s unlimited; rm -f /tmp/zt/hello.c
timeout ${T:-300} ${GDB:+gdb -batch -ex "break zb_trapbt" -ex run -ex "bt 30" --args} /data/zig2 build-obj -ofmt=c -OReleaseSmall --name hello -femit-bin=/tmp/zt/hello.c -target x86_64-linux --zig-lib-dir lib /tmp/zt/hello.zig 2>&1 | grep -v "^\[New\|^\[Thread\|^Using host" | head -${N:-40} | cut -c1-200
echo rc ${PIPESTATUS[0]}
