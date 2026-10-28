#!/usr/bin/env bash
# Publish the working tree as the public release repo SymSAT-1.0 (MIT): every tracked and untracked file except
# `context/` (conversation exports and Claude memory: private), as ONE commit on top of the previous release commit
# (the public repo keeps a release history; the private repo keeps the full history). Needs `gh auth login`.
#   scripts/release.sh [MESSAGE]      remote name `public`, repo lioncash3k6-ux/SymSAT-1.0, branch main
set -euo pipefail
REPO="$HOME/monster"
PUB="${SYMSAT_PUBLIC_REPO:-lioncash3k6-ux/SymSAT-1.0}"
cd "$REPO"
git remote get-url public >/dev/null 2>&1 || git remote add public "git@github.com:$PUB.git"
idx=$(mktemp "$HOME/.local/state/symsat/release-index.XXXXXX"); trap 'rm -f "$idx"' EXIT
cp .git/index "$idx"
GIT_INDEX_FILE="$idx" git rm -r -q --cached context >/dev/null 2>&1 || true
GIT_INDEX_FILE="$idx" git add -A -- . ':(exclude)context' ':(exclude)context/**'
GIT_INDEX_FILE="$idx" git rm -r -q --cached --ignore-unmatch context >/dev/null 2>&1 || true
tree=$(GIT_INDEX_FILE="$idx" git write-tree)
git fetch -q public main 2>/dev/null || true
parents=()
prev=$(git rev-parse -q --verify refs/remotes/public/main || true)
[ -n "$prev" ] && parents=(-p "$prev")
msg="${1:-SymSAT 1.0 release $(date -u +%FT%TZ) (main $(git rev-parse --short HEAD))}"
commit=$(git commit-tree "$tree" "${parents[@]}" -m "$msg")
git push -q public "$commit:refs/heads/main"
echo "released $(git rev-parse --short "$commit") to $PUB (tree without context/)"
