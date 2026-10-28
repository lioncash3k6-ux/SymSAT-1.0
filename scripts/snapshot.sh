#!/bin/bash
# Back up EVERYTHING in ~/monster (tracked and untracked files, minus .gitignore) to branch `backup/auto` on GitHub,
# after refreshing the exported chat context (context/chats/). It never touches HEAD, the index or main, and it is
# ungated on purpose: this is the safety net, so it never waits for builds or tests.
# Runs from the systemd user timer symsat-snapshot.timer (every 10 min) and from Claude Code hooks.
# usage: scripts/snapshot.sh [--debounce SECONDS]      (skip if the last snapshot is younger than SECONDS)
# recover: git fetch symsat backup/auto && git log symsat/backup/auto
set -u
REPO="$HOME/monster"
STATE="$HOME/.local/state/symsat"
mkdir -p "$STATE"
LOG="$STATE/snapshot.log"
cd "$REPO" || exit 0

if [ "${1:-}" = "--debounce" ] && [ -f "$STATE/last_snapshot_epoch" ]; then
  last=$(cat "$STATE/last_snapshot_epoch" 2>/dev/null || echo 0)
  [ $(( $(date +%s) - last )) -lt "${2:-120}" ] && exit 0
fi
exec 9>"$STATE/snapshot.lock"
flock -w 120 9 || { echo "$(date -u +%FT%TZ) lock busy, skipped" >> "$LOG"; exit 0; }

"$REPO/scripts/export_context.sh" >> "$LOG" 2>&1

idx=$(mktemp "$STATE/index.XXXXXX")
trap 'rm -f "$idx"' EXIT
cp "$REPO/.git/index" "$idx" 2>/dev/null || true
GIT_INDEX_FILE="$idx" git add -A -- . 2>>"$LOG"
# never snapshot a file GitHub would reject (100 MB limit), tracked or not (on 2026-10-28 six 0.3-1.5 GB proof
# files got committed to main and blocked every push for 9 hours)
big=()
while IFS= read -r -d "" f; do
  [ -f "$f" ] && [ "$(stat -c %s "$f")" -gt 95000000 ] && big+=("$f")
done < <(GIT_INDEX_FILE="$idx" git ls-files -z)
[ "${#big[@]}" -gt 0 ] && GIT_INDEX_FILE="$idx" git rm -q --cached -- "${big[@]}" 2>>"$LOG"
tree=$(GIT_INDEX_FILE="$idx" git write-tree) || exit 0

prev=$(git rev-parse -q --verify refs/heads/backup/auto)
if [ -n "$prev" ] && [ "$(git rev-parse "$prev^{tree}")" = "$tree" ]; then
  date +%s > "$STATE/last_snapshot_epoch"
  exit 0
fi
parents=(-p HEAD)
[ -n "$prev" ] && parents=(-p "$prev" -p HEAD)
msg="snapshot $(date -u +%FT%TZ) on main $(git rev-parse --short HEAD) ($(git status --porcelain | wc -l) uncommitted paths)"
commit=$(git commit-tree "$tree" "${parents[@]}" -m "$msg") || exit 0
git update-ref refs/heads/backup/auto "$commit"
short=$(git rev-parse --short "$commit")
if timeout 120 git push -q --force symsat refs/heads/backup/auto:refs/heads/backup/auto 2>>"$LOG"; then
  echo "$(date -u +%FT%TZ) pushed backup/auto $short" >> "$LOG"
  echo "$(date -u +%FT%TZ) ok $short" > "$STATE/last_snapshot"
else
  echo "$(date -u +%FT%TZ) PUSH FAILED (local backup/auto is $short)" >> "$LOG"
  echo "$(date -u +%FT%TZ) PUSH FAILED $short" > "$STATE/last_snapshot"
fi
date +%s > "$STATE/last_snapshot_epoch"
