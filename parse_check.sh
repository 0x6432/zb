#!/bin/bash
# Parse every .zig file in a Zig source tree with zb's parser (ZB_PARSE_ONLY=1).
root=${1:-zig-0.16.0}; ok=0; fail=0
for f in $(find "$root" -name '*.zig'); do
  if ZB_PARSE_ONLY=1 ./zb "$f" >/dev/null 2>/tmp/zb_perr; then ok=$((ok+1)); else fail=$((fail+1)); head -1 /tmp/zb_perr; fi
done
echo "parsed $ok files, $fail failures"
