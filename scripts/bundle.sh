#!/usr/bin/env bash
# Build a self-contained bundle for running gluing shards on other machines (CLAUDE.md: "Heavy jobs", README "--shard").
#   scripts/bundle.sh OUT.tar.gz          -> binary + catalogues + covers (symlinks dereferenced) + run_shard.sh
# On a worker (any x86-64 Linux with AVX, >= 1 GB RAM per 12 workers):
#   tar xzf OUT.tar.gz && cd symsat-bundle && ./run_shard.sh D I N [WORKERS]     # e.g. ./run_shard.sh 10 3 8 16
# which writes shard_d{D}_{I}of{N}/tasks.jsonl. Bring every shard's tasks.jsonl back, concatenate them into the
# stage's --out directory (results/overnight/d10_certified/tasks.jsonl) and run the stage command with --resume: it
# re-solves nothing, re-runs lines that are not certified, and writes summary.json with complete:true.
set -euo pipefail
out=${1:?usage: scripts/bundle.sh OUT.tar.gz}
root=$(cd "$(dirname "$0")/.." && pwd)
tmp=$(mktemp -d)
b="$tmp/symsat-bundle"
mkdir -p "$b/catalogs" "$b/covers"
cp "$root/target/release/monster" "$b/"
cp "$root/verified/.lake/build/bin/checker" "$b/"      # the Lean checker (x86-64 Linux, glibc only)
cat=${SYMSAT_CATALOGS:-$HOME/cascade-solver-ramsey-v4-algebraic/v5/catalogs}
cp -rL "$cat/r35" "$cat/r44" "$b/catalogs/"
cp -L "$root"/results/covers_r45/*.txt "$b/covers/"
cat > "$b/run_shard.sh" <<'EOF'
#!/usr/bin/env bash
# run_shard.sh D I N [WORKERS]: certified unit-mode shard I of N of the degree-D gluing stage of R(4,5) <= 25
set -euo pipefail
d=${1:?degree}; i=${2:?shard index}; n=${3:?shard count}; w=${4:-$(nproc)}
case "$d" in
  10) ga=6; gb=6 ;;
  12) ga=6; gb=8 ;;
  *) echo "covers are tuned for d=10 (6,6) and d=12 (6,8); pass GA GB by editing this script" >&2; exit 2 ;;
esac
here=$(cd "$(dirname "$0")" && pwd)
exec "$here/monster" glue --s 4 --t 5 --n 25 --route all --d "$d" --mode unit --catalogs "$here/catalogs" \
  --covers "$here/covers" --gray-a "$ga" --gray-b "$gb" --workers "$w" --check-every 1 --quiet \
  --shard "$i/$n" --out "$here/shard_d${d}_${i}of${n}" --resume
EOF
chmod +x "$b/run_shard.sh"
cat > "$b/run_lean_shard.sh" <<'EOF'
#!/usr/bin/env bash
# run_lean_shard.sh D I N [WORKERS] [LEAN_JOBS]: Lean-verified shard I of N of the degree-D stage (unit-lean-stage: cube
# export + the verified checker in batches; proofs deleted after verification). Output: lean_d{D}_{I}of{N}/ with
# verified.jsonl (merge into the main stage's file) and rec/*.rec (copy into one directory for assemble-spec --from-record).
# Resumable: run again after an interruption.
set -euo pipefail
d=${1:?degree}; i=${2:?shard index}; n=${3:?shard count}; c=$(nproc); w=${4:-$(( c > 2 ? c * 6 / 10 : 1 ))}; j=${5:-$(( c - w > 0 ? c - w : 1 ))}
case "$d" in
  8|10) ga=6; gb=6 ;;
  12) ga=6; gb=8 ;;
  *) echo "covers are tuned for d=8/10 (6,6) and d=12 (6,8)" >&2; exit 2 ;;
esac
here=$(cd "$(dirname "$0")" && pwd)
exec "$here/monster" unit-lean-stage --s 4 --t 5 --n 25 --d "$d" --catalogs "$here/catalogs" --covers "$here/covers" \
  --gray-a "$ga" --gray-b "$gb" --workers "$w" --lean-jobs "$j" --batch 6 --shard "$i/$n" --resume \
  --lean "$here/checker" --out "$here/lean_d${d}_${i}of${n}"
EOF
chmod +x "$b/run_lean_shard.sh"
tar czf "$out" -C "$tmp" symsat-bundle
rm -rf "$tmp"
ls -la "$out"
