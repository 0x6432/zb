#!/bin/sh
# Build the zb `zig` driver -> bin/zig (needs ./zb and qbe-1.2/qbe)
set -e
cd "$(dirname "$0")/.."
mkdir -p bin build
./zb driver/zig.zig -o build/zigdrv.ssa
${QBE:-qbe-1.2/qbe} -o build/zigdrv.s build/zigdrv.ssa
cc -o bin/zig build/zigdrv.s build/zigdrv.ssa.asm.s tools/zbrt.c -lm
echo "built bin/zig"
