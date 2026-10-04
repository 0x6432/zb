#!/bin/bash
# stage.sh IN.c OUTBIN : split zig C output, compile with cc, link (uses ${RT:-/data/compiler_rt17.c})
set -e; in=$1; out=$2; d=/data/zsplit_$(basename $out); rm -rf $d
python3 /data/zb/tools/csplit.py $in $d 10
cd $d; s=$(date +%s)
ls zig2_*.c | xargs -P ${J:-2} -I{} sh -c 'cc -c -std=c99 -O${O:-1} -w -fno-stack-protector -fno-strict-aliasing -fno-tree-sra -I${ZLIB:-/data/zig17-src/lib} -o $(basename {} .c).o {} 2>&1 | grep -m3 error || true'
cc -c -std=c99 -O1 -w -fno-stack-protector -fno-strict-aliasing -fno-tree-sra -I${ZLIB:-/data/zig17-src/lib} -o compiler_rt.o ${RT:-/data/compiler_rt17.c}
cc -o $out zig2_*.o compiler_rt.o -Wl,-z,stack-size=0x10000000 -pthread -lm
echo "built $out in $(( $(date +%s) - s ))s"; rm -f zig2_*.c zig2.h
