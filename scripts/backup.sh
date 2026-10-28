#!/bin/bash
# Superseded (2026-10-26). The old hourly cron committed straight to main, which once pushed untested code (05:17).
# Backups are now: scripts/snapshot.sh (every file to branch backup/auto; timer symsat-snapshot.timer every 10 min and
# Claude Code hooks) plus scripts/autocommit_hook.sh (gated commits to main). Kept so an old crontab line stays safe.
exec "$HOME/monster/scripts/snapshot.sh"
