#!/bin/sh
# usage: next.sh "commit msg"
cd /data/zb && rm -f zb; make -s GC=1 2>&1 | grep -i '\berror\b'; r=$(./run_tests.sh | tail -1); echo "$r"
case "$r" in *"failed 0"*) [ -n "$1" ] && git commit -qam "$1";; *) echo "TESTS FAILING - not committed"; exit 1;; esac
timeout 900 /tmp/zc.sh 12 2>&1 | grep -v 'warning\|xgetbv'
