#!/bin/bash
f=$1; shift
/data/zb/zb "$f" -o /tmp/t/o.ssa "$@" || exit 1
/data/zb/qbe-1.2/qbe /tmp/t/o.ssa > /tmp/t/o.s || exit 2
cc -o /tmp/t/o /tmp/t/o.s -lm || exit 3
/tmp/t/o; echo "exit=$?"
