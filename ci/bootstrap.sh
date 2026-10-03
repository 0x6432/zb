#!/usr/bin/env bash
# Full zb bootstrap pipeline (portable version of tools/*.sh).
#   ZIGSRC  : Zig 0.16.0 source tree (with lib/)          default: $WORK/zig-0.16.0
#   QBE     : qbe binary                                  default: $WORK/qbe-1.2/qbe
#   WORK    : scratch dir for big artifacts               default: $PWD/work
# Stages: zb -> zig2 (QBE) -> compiler_rt.c + zig2_self.c -> zig3 (cc) -> zig3_self.c -> zig4 -> zig4_self.c
# Checks: zig3_self.c == zig4_self.c (fixed point); zig2_self.c vs zig3_self.c diff report; hello world runs.
set -euo pipefail
ZB=$(cd "$(dirname "$0")/.." && pwd)
WORK=${WORK:-$PWD/work}; mkdir -p "$WORK"; WORK=$(cd "$WORK" && pwd)
ZIGSRC=$(cd "${ZIGSRC:-$WORK/zig-0.16.0}" && pwd); QBE=$(readlink -f "${QBE:-$WORK/qbe-1.2/qbe}"); export QBE
STAGE=${1:-all}
ulimit -s unlimited || true
log() { echo "::group::$*" 2>/dev/null || true; echo "== $* ($(date +%T))"; }
end() { echo "::endgroup::" 2>/dev/null || true; }
cp "$ZB/tools/config.zig" "$ZIGSRC/config.zig"
CCFLAGS="-std=c99 -O${OPT:-1} -w -fno-stack-protector -fno-strict-aliasing -fno-tree-sra -I$ZIGSRC/lib"

build_zb() { log "build zb"; make -C "$ZB" GC=1 -s; (cd "$ZB" && ./run_tests.sh | tail -3); end; }

build_zig2() {
  log "zb: Zig compiler -> QBE IL"
  (cd "$ZIGSRC" && "$ZB/zb" src/main.zig -o "$WORK/zig2.ssa" --std-dir lib/std -Mbuild_options=config.zig -Maro=lib/compiler/aro/aro.zig 2>&1 | grep -v 'note:' | head -20)
  log "qbe + as + link zig2"
  "$QBE" -o "$WORK/zig2.s" "$WORK/zig2.ssa"
  cc -c -o "$WORK/zig2.o" "$WORK/zig2.s" 2>&1 | grep -v 'Warning\|Assembler messages' | head -5 || true
  cc -O1 -c -o "$WORK/zbrt.o" "$ZB/tools/zbrt.c"
  cc -o "$WORK/zig2" "$WORK/zig2.o" "$WORK/zbrt.o" -lm -pthread -Wl,-z,stack-size=0x10000000
  rm -f "$WORK/zig2.ssa" "$WORK/zig2.s" "$WORK/zig2.o"; end
}

selfc() { # selfc BIN OUT.c
  (cd "$ZIGSRC" && "$1" build-exe -ofmt=c -lc -OReleaseSmall --name zig2 -femit-bin="$2" -target x86_64-linux --zig-lib-dir lib \
     --dep build_options --dep aro -Mroot=src/main.zig -Mbuild_options=config.zig -Maro=lib/compiler/aro/aro.zig)
}
stagebin() { # stagebin IN.c OUTBIN : split + cc + link
  local d="$WORK/split_$(basename "$2")"; rm -rf "$d"
  python3 "$ZB/tools/csplit.py" "$1" "$d" ${CHUNKS:-10}
  (cd "$d" && ls zig2_*.c | xargs -P "${JOBS:-$(nproc)}" -I{} sh -c "cc -c $CCFLAGS -o \$(basename {} .c).o {}")
  cc -c $CCFLAGS -o "$d/compiler_rt.o" "$WORK/compiler_rt.c"
  cc -o "$2" "$d"/zig2_*.o "$d/compiler_rt.o" -Wl,-z,stack-size=0x10000000 -pthread -lm
  rm -rf "$d"
}
hello() { # hello BIN
  printf 'const std = @import("std");\npub fn main() void {\n    var x: u32 = 6;\n    _ = &x;\n    std.debug.print("hello {d}\\n", .{x * 7});\n}\n' > "$WORK/hello.zig"
  (cd "$ZIGSRC" && "$1" build-exe -ofmt=c -lc -OReleaseSmall --name hello -femit-bin="$WORK/hello.c" -target x86_64-linux --zig-lib-dir lib "$WORK/hello.zig")
  cc -w -I"$ZIGSRC/lib" -o "$WORK/hello" "$WORK/hello.c"; "$WORK/hello" 2>&1 | tee "$WORK/hello.out"; grep -q "hello 42" "$WORK/hello.out"
}

stages() {
  log "zig2: compiler_rt.c"
  (cd "$ZIGSRC" && "$WORK/zig2" build-obj -ofmt=c -OReleaseSmall --name compiler_rt -femit-bin="$WORK/compiler_rt.c" -target x86_64-linux --zig-lib-dir lib -Mroot=lib/compiler_rt.zig); end
  log "zig2: hello world"; hello "$WORK/zig2"; end
  log "zig2: compiler -> zig2_self.c"; selfc "$WORK/zig2" "$WORK/zig2_self.c"; end
  log "cc: zig3"; stagebin "$WORK/zig2_self.c" "$WORK/zig3"; end
  log "zig3: hello world"; hello "$WORK/zig3"; end
  log "zig3: compiler -> zig3_self.c"; selfc "$WORK/zig3" "$WORK/zig3_self.c"; end
  log "cc: zig4"; stagebin "$WORK/zig3_self.c" "$WORK/zig4"; end
  log "zig4: compiler -> zig4_self.c"; selfc "$WORK/zig4" "$WORK/zig4_self.c"; end
}

compare() {
  log "binary comparison"
  local rc=0
  if cmp "$WORK/zig3_self.c" "$WORK/zig4_self.c"; then echo "FIXED POINT: zig3_self.c == zig4_self.c"; else echo "MISMATCH zig3 vs zig4"; rc=1; fi
  if cmp -s "$WORK/zig2_self.c" "$WORK/zig3_self.c"; then echo "zig2_self.c == zig3_self.c (zb-built zig2 is exact)"
  else
    sed -E 's/[0-9]+/N/g' "$WORK/zig2_self.c" > "$WORK/n2"; sed -E 's/[0-9]+/N/g' "$WORK/zig3_self.c" > "$WORK/n3"
    echo "zig2 vs zig3: $(diff "$WORK/n2" "$WORK/n3" | grep -c '^<' || true) lines differ modulo numbering"; rm -f "$WORK/n2" "$WORK/n3"
  fi
  sha256sum "$WORK"/zig*_self.c "$WORK/compiler_rt.c" | tee "$WORK/SHA256SUMS"
  end; return $rc
}

stage3() { # Zig's own build system + tools, using the bootstrapped compiler
  log "zig4 build (stage3, self-hosted x86_64 backend)"
  (cd "$ZIGSRC" && "$WORK/zig4" build -p "$WORK/stage3" -Dno-lib --zig-lib-dir lib) || { echo "stage3 build failed"; return 1; }
  local Z="$WORK/stage3/bin/zig"
  "$Z" version
  (cd "$ZIGSRC" && "$Z" fmt --check lib/std/mem.zig src/main.zig && echo "zig fmt --check OK")
  (cd "$ZIGSRC" && "$Z" ast-check src/Sema.zig && echo "zig ast-check OK")
  (cd "$WORK" && "$Z" run --zig-lib-dir "$ZIGSRC/lib" hello.zig)
  (cd "$ZIGSRC" && "$Z" test --zig-lib-dir lib lib/std/math/big/int.zig 2>&1 | tail -3) || true
  end
}

case "$STAGE" in
  zb) build_zb ;;
  zig2) build_zig2 ;;
  stages) stages ;;
  compare) compare ;;
  stage3) stage3 ;;
  all) build_zb; build_zig2; stages; compare; stage3 || true ;;
esac
