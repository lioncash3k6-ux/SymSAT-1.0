#!/bin/bash
# One-time setup of the always-on backups. Run it yourself (it enables persistence on this box):
#   ~/monster/scripts/install_backups.sh [--swap 16G]
# - linger for this user: the systemd user manager, and with it the snapshot timer, capped jobs (scripts/capped.sh)
#   and tmux, keep running with nobody logged in
# - systemd user timer symsat-snapshot.timer: scripts/snapshot.sh every 10 minutes (every file to branch backup/auto)
# - optional swap file as a safety margin against a global OOM (capped jobs use MemorySwapMax=0 and never swap)
# Undo: systemctl --user disable --now symsat-snapshot.timer; sudo loginctl disable-linger $USER; sudo swapoff /swapfile
set -e
sudo loginctl enable-linger "$USER"
mkdir -p "$HOME/.config/systemd/user"
cp "$HOME/monster/scripts/systemd/symsat-snapshot.service" "$HOME/monster/scripts/systemd/symsat-snapshot.timer" "$HOME/.config/systemd/user/"
systemctl --user daemon-reload
systemctl --user enable --now symsat-snapshot.timer
# Claude Code hooks (snapshot after edits, gated commit at the end of every turn, session brief)
mkdir -p "$HOME/.claude" && cp "$HOME/monster/scripts/claude-settings.json" "$HOME/.claude/settings.json"
if [ "${1:-}" = "--swap" ] && ! swapon --show | grep -q /swapfile; then
  sudo fallocate -l "${2:-16G}" /swapfile
  sudo chmod 600 /swapfile
  sudo mkswap /swapfile >/dev/null
  sudo swapon /swapfile
  grep -q '^/swapfile ' /etc/fstab || echo '/swapfile none swap sw 0 0' | sudo tee -a /etc/fstab >/dev/null
fi
echo "linger: $(loginctl show-user "$USER" -p Linger --value)"
systemctl --user list-timers symsat-snapshot.timer --no-pager | head -2
swapon --show
