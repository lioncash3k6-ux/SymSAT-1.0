#!/bin/bash
# Run a long or memory-heavy job (Lean kernel checks, big solves, overnight runs) as its own systemd user unit with a
# hard memory cap. A blow-up then kills only that job, never tmux or the Claude session (CONTINUE.md 5b'), and the job
# survives logouts (linger is on). Do NOT use `setsid nohup` instead: it stays in the session's cgroup.
# usage:  scripts/capped.sh NAME MEMORY COMMAND [ARGS...]    e.g. scripts/capped.sh kernel-r44 40G lake env lean X.lean
# status: systemctl --user status symsat-NAME   logs: journalctl --user -u symsat-NAME   stop: systemctl --user stop symsat-NAME
set -eu
[ $# -ge 3 ] || { echo "usage: $0 NAME MEMORY COMMAND [ARGS...]" >&2; exit 2; }
name="symsat-$1"
mem="$2"
shift 2
exec systemd-run --user --unit="$name" --same-dir --collect -E HOME -E PATH -p MemoryMax="$mem" -p MemorySwapMax=0 "$@"
