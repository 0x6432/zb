#!/bin/bash
# run full compile with current ./zb, sample peak RSS
cd /data/zig-src
start=$(date +%s)
/data/zb/zb src/main.zig -o /tmp/zig2.ssa --std-dir lib/std -Mbuild_options=config.zig -Maro=lib/compiler/aro/aro.zig > /tmp/zcg.log 2>&1 &
pid=$!; peak=0
while kill -0 $pid 2>/dev/null; do r=$(awk '/VmRSS/{print $2}' /proc/$pid/status 2>/dev/null); [ -n "$r" ] && [ "$r" -gt "$peak" ] && peak=$r; sleep 1; done
wait $pid; ec=$?
echo "exit $ec  peakRSS ${peak}kB  time $(( $(date +%s)-start ))s  out $(stat -c %s /tmp/zig2.ssa)"
grep -v "warning\|xgetbv" /tmp/zcg.log | head -${1:-10} | cut -c1-300
