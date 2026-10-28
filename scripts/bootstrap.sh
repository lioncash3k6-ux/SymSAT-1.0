#!/usr/bin/env bash
# One command from a bare Linux box (x86-64 or aarch64; Ubuntu/Debian, or Termux through proot-distro Ubuntu) to a
# running Lean-stage shard of R(4,5) <= 25:
#   curl -fsSL https://raw.githubusercontent.com/lioncash3k6-ux/SymSAT-1.0/main/scripts/bootstrap.sh | bash -s -- [OPTIONS]
#   monster bootstrap [OPTIONS]        (the same script, embedded in the binary: from a bundle, no download needed)
#   scripts/bootstrap.sh [--dir DIR] [--no-run] [--d D] [--shard I/N] [--workers W] [--lean-jobs J]
# What it does (each step is skipped when already done): apt packages (git, build-essential, curl, jq), rustup (Rust),
# elan (Lean, toolchain pinned by verified/lean-toolchain), clone of the public SymSAT-1.0 repo (SYMSAT_REPO overrides)
# and of the public catalogue repo, `cargo build --release`, `lake build` (the verified checker), and then,
# unless --no-run, `monster unit-lean-stage --d D --shard I/N` as a plain background process writing to
# DIR/monster/results/leanstage/d{D}_shard{I}of{N}/ (resumable: run the same command again after an interruption).
# Bring back from a finished shard: verified.jsonl (merge: concatenate into the main stage's verified.jsonl) and the
# rec/*.rec files (copy into one directory for `monster assemble-spec --from-record DIR`).
# Termux (Android) without proot: Rust works (`pkg install rust`) but Lean does not run on bionic; install
# proot-distro (`pkg install proot-distro && proot-distro install ubuntu && proot-distro login ubuntu`) and run this
# script inside. The phone then contributes solving AND Lean verification like any Linux box (aarch64 Lean releases).
set -euo pipefail
dir="$HOME"; run=1; d=10; shard="0/1"; workers=""; leanjobs=""
while [ $# -gt 0 ]; do
  case "$1" in
    --dir) dir="$2"; shift 2 ;;
    --no-run) run=0; shift ;;
    --d) d="$2"; shift 2 ;;
    --shard) shard="$2"; shift 2 ;;
    --workers) workers="$2"; shift 2 ;;
    --lean-jobs) leanjobs="$2"; shift 2 ;;
    *) echo "unknown option $1" >&2; exit 2 ;;
  esac
done
if [ -n "${TERMUX_VERSION:-}" ] && [ ! -e /etc/debian_version ]; then
  echo "Termux detected: Lean needs a glibc userland. Run:  pkg install proot-distro && proot-distro install ubuntu && proot-distro login ubuntu" >&2
  echo "then inside Ubuntu:  apt update && apt install -y curl && curl -fsSL https://raw.githubusercontent.com/lioncash3k6-ux/SymSAT-1.0/main/scripts/bootstrap.sh | bash -s -- $*" >&2
  exit 2
fi
arch=$(uname -m)
case "$arch" in x86_64|aarch64) ;; *) echo "unsupported architecture $arch (need x86_64 or aarch64)" >&2; exit 2 ;; esac
sudo=""; [ "$(id -u)" != 0 ] && command -v sudo >/dev/null && sudo=sudo
if command -v apt-get >/dev/null; then
  need=""; for p in git build-essential curl jq ca-certificates; do dpkg -s "$p" >/dev/null 2>&1 || need="$need $p"; done
  if [ -n "$need" ]; then $sudo apt-get update -q && $sudo apt-get install -y -q $need; fi
fi
if [ ! -x "$HOME/.cargo/bin/cargo" ]; then
  curl -sSf https://sh.rustup.rs | sh -s -- -y --profile minimal
fi
# shellcheck disable=SC1091
source "$HOME/.cargo/env"
if [ ! -x "$HOME/.elan/bin/lake" ]; then
  curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | bash -s -- -y --default-toolchain none
fi
# shellcheck disable=SC1091
source "$HOME/.elan/env"
mkdir -p "$dir"
if [ ! -d "$dir/monster/.git" ]; then
  git clone "${SYMSAT_REPO:-https://github.com/lioncash3k6-ux/SymSAT-1.0.git}" "$dir/monster"
fi
if [ ! -d "$dir/cascade-solver-ramsey-v4-algebraic/.git" ]; then
  git clone --depth 1 https://github.com/lioncash3k6-ux/cascade-solver-ramsey-v4-algebraic "$dir/cascade-solver-ramsey-v4-algebraic"
fi
cd "$dir/monster"
cargo build --release
(cd verified && lake build)
./target/release/monster full --s 3 --t 3 --n 6 --patterns --lemmas --proof | tail -1
echo "bootstrap: built $(./target/release/monster --version 2>/dev/null || echo monster) and verified/.lake/build/bin/checker"
[ "$run" = 1 ] || exit 0
case "$d" in 10) ga=6; gb=6 ;; 12) ga=6; gb=8 ;; 8) ga=6; gb=6 ;; *) echo "pass --d 8|10|12" >&2; exit 2 ;; esac
cores=$(nproc); w=${workers:-$(( cores > 2 ? cores * 6 / 10 : 1 ))}; j=${leanjobs:-$(( cores - w > 0 ? cores - w : 1 ))}
i=${shard%/*}; n=${shard#*/}
out="results/leanstage/d${d}_shard${i}of${n}"
mkdir -p "$out"
echo "bootstrap: starting unit-lean-stage d=$d shard $shard, $w workers, $j Lean jobs -> $out (log: $out/stage.log)"
nohup ./target/release/monster unit-lean-stage --s 4 --t 5 --n 25 --d "$d" --catalogs "$dir/cascade-solver-ramsey-v4-algebraic/v5/catalogs" \
  --covers results/covers_r45 --gray-a "$ga" --gray-b "$gb" --out "$out" --workers "$w" --lean-jobs "$j" --batch 6 \
  --shard "$shard" --resume --lean verified/.lake/build/bin/checker >> "$out/stage.log" 2>&1 &
echo "bootstrap: pid $!; progress: wc -l $out/verified.jsonl"
