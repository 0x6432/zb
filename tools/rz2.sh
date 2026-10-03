#!/bin/bash
# run zig2 under gdb with given args (cwd zig-src), stop at trap: rz2.sh build-exe ...
cd /data/zig-src && ulimit -s unlimited
timeout ${T:-600} gdb -batch -ex "break zb_trapbt" -ex run -ex "bt ${BT:-14}" --args /data/zig2 "$@" 2>&1 | grep -v "^\[New\|^\[Thread\|^Using host\|^Breakpoint 1 at\|^  #" | sed 's/ () at \/vercel\/sandbox\/data\/zig-src\// /' | head -${N:-40} | cut -c1-200
