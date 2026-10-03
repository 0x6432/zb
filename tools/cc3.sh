#!/bin/bash
# compile split zig2 C chunks (/data/z3) + compiler_rt.c and link /data/zig3
cd /data/z3 && s=$(date +%s)
ls zig2_*.c | xargs -P ${J:-2} -I{} sh -c 'cc -c -std=c99 -O${O:-1} -w -fno-stack-protector -I/data/zig-src/lib -o $(basename {} .c).o {} 2>&1 | grep -m3 error'
cc -c -std=c99 -O1 -w -fno-stack-protector -I/data/zig-src/lib -o compiler_rt.o /data/compiler_rt.c
cc -o /data/zig3 zig2_*.o compiler_rt.o -Wl,-z,stack-size=0x10000000 -pthread -lm 2>&1 | head -20
echo "done $(( $(date +%s) - s ))s"; ls -la /data/zig3
