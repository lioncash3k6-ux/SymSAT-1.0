#!/bin/bash
# Claude Code Stop hook (configured in ~/.claude/settings.json; runs whenever Claude finishes a turn):
#  1. snapshot every file to branch backup/auto (always, ungated, see snapshot.sh);
#  2. if code changed but CONTINUE.md did not, block once so Claude updates the hand-off docs first;
#  3. commit everything to main and push, but only if cargo build, cargo test (incl. tests/regression.rs) and, when
#     verified/ changed, `lake build` pass. Otherwise main is left alone and Claude is told why (once).
# Input: hook JSON on stdin (stop_hook_active is true when Claude is already continuing because of this hook).
# Test without committing: echo '{}' | SYMSAT_HOOK_DRYRUN=1 scripts/autocommit_hook.sh
set -u
REPO="$HOME/monster"
STATE="$HOME/.local/state/symsat"
mkdir -p "$STATE"
LOG="$STATE/autocommit.log"
input=$(cat 2>/dev/null || true)
active=$(printf '%s' "$input" | jq -r '.stop_hook_active // false' 2>/dev/null || echo false)
cd "$REPO" || exit 0
exec 8>"$STATE/autocommit.lock"
flock -w 600 8 || exit 0

"$REPO/scripts/snapshot.sh" >/dev/null 2>&1

status=$(git status --porcelain)
[ -n "$status" ] || exit 0
paths=$(printf '%s\n' "$status" | awk '{print $NF}')
code=$(printf '%s\n' "$paths" | grep -E '^(src/|tests/|verified/(MonsterVerified/|Main\.lean|MonsterVerified\.lean|lakefile)|scripts/|Cargo\.(toml|lock)$|\.cargo/)' || true)
docs=$(printf '%s\n' "$paths" | grep -E '^CONTINUE\.md$' || true)

block() { jq -n --arg r "$1" '{decision: "block", reason: $r}'; exit 0; }
say() { jq -n --arg m "$1" '{systemMessage: $m}'; exit 0; }

if [ -n "$code" ] && [ -z "$docs" ] && [ "$active" != true ]; then
  block "SymSAT auto-commit: code changed ($(printf '%s ' $code | cut -c1-200)) but CONTINUE.md was not updated. Update CONTINUE.md (what changed, current state, next step), and README.md / RESULTS.md / CLAUDE.md if usage, numbers or rules changed. Then finish; this hook then gates and commits to main."
fi

why=""
if [ -n "$code" ]; then
  source "$HOME/.cargo/env"
  if ! out=$(cargo build --release 2>&1); then
    why="cargo build failed: $(printf '%s\n' "$out" | grep -E '^error' | head -3 | tr '\n' ' ')"
  elif ! out=$(timeout 900 cargo test --release 2>&1); then
    why="cargo test failed: $(printf '%s\n' "$out" | grep -E 'FAILED|panicked' | head -4 | tr '\n' ' ')"
  elif printf '%s\n' "$code" | grep -q '^verified/'; then
    source "$HOME/.elan/env"
    if ! out=$(cd verified && timeout 900 lake build 2>&1); then
      why="lake build failed: $(printf '%s\n' "$out" | grep -E 'error' | head -3 | tr '\n' ' ')"
    fi
  fi
fi
if [ -n "$why" ]; then
  echo "$(date -u +%FT%TZ) main NOT committed: $why" >> "$LOG"
  [ "$active" != true ] && block "SymSAT auto-commit: $why. Fix it or revert the change before finishing. All files are already in the backup/auto snapshot."
  say "SymSAT: main NOT committed ($why). The work is in the backup/auto snapshot."
fi

[ -n "${SYMSAT_HOOK_DRYRUN:-}" ] && say "DRY RUN: gate passed; would commit $(printf '%s\n' "$paths" | wc -l) paths to main and push."
git add -A
# never commit a file GitHub would reject (100 MB limit); it stays on disk, untracked (on 2026-10-28 six 0.3-1.5 GB
# proof files got committed to main and blocked every push for 9 hours)
big=()
while IFS= read -r -d "" f; do
  [ -f "$f" ] && [ "$(stat -c %s "$f")" -gt 95000000 ] && big+=("$f")
done < <(git ls-files -z)
[ "${#big[@]}" -gt 0 ] && { git rm -q --cached -- "${big[@]}"; echo "$(date -u +%FT%TZ) skipped oversized: ${big[*]}" >> "$LOG"; }
n=$(git diff --cached --name-only | wc -l)
list=$(git diff --cached --name-only | head -15)
git commit -q -m "auto: $(date -u +%FT%TZ), $n files$([ -n "$code" ] && echo ', build+tests passed')

$list

Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>" || exit 0
c=$(git rev-parse --short HEAD)
if timeout 120 git push -q symsat main 2>>"$LOG"; then r=pushed; else r="PUSH FAILED"; fi
echo "$(date -u +%FT%TZ) main $c $r ($n files)" >> "$LOG"
say "SymSAT: main $c committed ($n files) and $r."
