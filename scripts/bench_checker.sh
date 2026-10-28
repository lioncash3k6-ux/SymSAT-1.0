#!/usr/bin/env bash
# bench_checker.sh BIN PROOF [RUNS]: min user CPU seconds of `BIN --lemma PROOF` and `BIN --parse PROOF` over RUNS runs
# (default 3). Use it to judge checker changes: wall time on a loaded box varies by 25%, the min of user time by ~3%.
set -euo pipefail
bin=${1:?checker binary}; proof=${2:?slrat proof}; runs=${3:-3}
best() { local m=999999; for _ in $(seq 1 "$runs"); do t=$( { /usr/bin/time -f "%U" "$bin" "$@" >/dev/null; } 2>&1 | tail -1 ); m=$(awk -v a="$m" -v b="$t" 'BEGIN{print (b<a)?b:a}'); done; echo "$m"; }
l=$(best --lemma "$proof"); p=$(best --parse "$proof")
awk -v l="$l" -v p="$p" -v f="$proof" 'BEGIN{printf "%s: lemma check %.2f s (min user of runs), parse only %.2f s (%.0f%%), check part %.2f s\n", f, l, p, 100*p/l, l-p}'
