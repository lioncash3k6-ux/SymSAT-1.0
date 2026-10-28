#!/bin/bash
# Claude Code SessionStart hook: print a short pickup brief, which Claude Code adds to the new session's context, and
# take a snapshot in the background (so the previous session's final transcript is exported and pushed).
REPO="$HOME/monster"
STATE="$HOME/.local/state/symsat"
cd "$REPO" 2>/dev/null || exit 0
setsid -f "$REPO/scripts/snapshot.sh" >/dev/null 2>&1 < /dev/null
echo "SymSAT pickup brief, $(date -u +%FT%TZ). Repo ~/monster = github lioncash3k6-ux/SymSAT, branch main."
echo "FIRST read ~/monster/CLAUDE.md and CONTINUE.md in full, then the newest file in ~/monster/context/chats/ (INDEX.md lists them)."
echo "main: $(git log -1 --format='%h %ci %s' | cut -c1-120)"
echo "uncommitted paths: $(git status --porcelain | wc -l); last snapshot (backup/auto): $(cat "$STATE/last_snapshot" 2>/dev/null || echo none)"
echo "snapshot timer: $(systemctl --user is-active symsat-snapshot.timer 2>/dev/null); linger: $(loginctl show-user "$USER" -p Linger --value 2>/dev/null)"
units=$(systemctl --user list-units --type=service --state=running --no-legend 'symsat-*' 2>/dev/null | awk '{print $1}' | tr '\n' ' ')
echo "running capped jobs: ${units:-none}; monster processes: $(pgrep -c -x monster 2>/dev/null || echo 0)"
fails=$(grep -h -E 'NOT committed|PUSH FAILED' "$STATE"/autocommit.log "$STATE"/snapshot.log 2>/dev/null | tail -3)
[ -n "$fails" ] && printf 'recent backup problems:\n%s\n' "$fails"
oom=$(journalctl --since "-24h" --no-pager -q 2>/dev/null | grep -c -i 'oom-kill' )
[ "${oom:-0}" -gt 0 ] && echo "WARNING: $oom OOM-kill journal lines in the last 24 h (journalctl --since -24h | grep -i oom)"
exit 0
