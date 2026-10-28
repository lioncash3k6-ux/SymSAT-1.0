#!/bin/bash
cd ~/monster
for inst in "4 4 17" "4 4 18" "3 5 14" "3 4 9"; do set -- $inst
  for lib in inline separate lift lift-inline; do
    ./target/release/monster bench --s $1 --t $2 --n $3 --samples 32 --patterns --lemmas --lib $lib 2>&1 | grep '^BENCH' | sed "s/^BENCH //;s/^{/{\"lib\":\"$lib\",/" >> results/bench/libmodes_2026-10-26.jsonl
  done
done
