#!/bin/bash
# Fixed progress suite (a few minutes). One JSON row per run in bench/progress.jsonl, tagged with the git commit.
set -u
cd "$HOME/monster" || exit 1
source "$HOME/.cargo/env"
cargo build --release >/dev/null 2>&1 || { echo "build failed"; exit 1; }
M=./target/release/monster
commit=$(git rev-parse --short HEAD)$(git diff --quiet || echo "+dirty")
ts=$(date -u +%FT%TZ)
row="{\"ts\":\"$ts\",\"commit\":\"$commit\""
for spec in "3 4 9" "3 5 14" "4 4 18"; do
  set -- $spec
  line=$(timeout 600 $M full --s $1 --t $2 --n $3 --patterns --lemmas --max-lbd 12 --proof | grep '^RESULT' | sed 's/^RESULT //')
  [ -z "$line" ] && line="{\"instance\":\"R($1,$2)/K$3\",\"result\":\"timeout\"}"
  row="$row,\"R$1$2_K$3\":$line"
done
# K25 propagation profile: 6000 conflicts from the cached verified library (deterministic node/call counts)
k25=$(timeout 1200 $M full --s 4 --t 5 --n 25 --patterns --books --library results/library_R45_K25_books.bin --budget 6000 2>/dev/null)
nodes=$(echo "$k25" | grep -o 'search nodes [0-9,]*' | tr -dc '0-9')
calls=$(echo "$k25" | grep -o '[0-9,]* embed calls' | tr -dc '0-9')
secs=$(echo "$k25" | grep '^RESULT' | grep -o '"secs":[0-9.]*' | cut -d: -f2)
row="$row,\"K25_6000\":{\"secs\":${secs:-null},\"nodes\":${nodes:-null},\"embed_calls\":${calls:-null}}"
# hybrid gluing, every task certified: R(3,6) <= 18
out=$(mktemp -d)
start=$(date +%s.%N)
hy=$(timeout 1200 $M glue --s 3 --t 6 --n 18 --route all --mode hybrid --books --check-every 1 --chunk 64 --workers 8 --out $out/h 2>&1 | sed 's/\x1b\[[0-9;]*m//g')
end=$(date +%s.%N)
ok=$(echo "$hy" | grep -c "UNSAT: every pair")
rm -rf $out
row="$row,\"hybrid_R36_N18_certified\":{\"ok\":$ok,\"wall\":$(echo "$end - $start" | bc)}}"

echo "$row" >> bench/progress.jsonl
echo "$row"
