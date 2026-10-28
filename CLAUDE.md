# Instructions for Claude: SymSAT (~/monster)

This machine runs one project: **SymSAT**, an exact Ramsey solver in Rust (binary `monster`) with a Lean 4 checker
whose soundness is proved (`verified/`). Repo: github `lioncash3k6-ux/SymSAT`, branch `main` (git remote `symsat`).
Older history: branch `monster-rust-solver` of `lioncash3k6-ux/cascade-solver`, an ancestor of SymSAT main (nothing
there that SymSAT lacks). `~/CLAUDE.md` is a symlink to this file.

## At the start of every session, before the first real answer
0. Know the server: one VM (`srv-7q6ax`, 16 vCPU Ivy Bridge, 62 GiB RAM, 15 GiB swap, 1.3 TB disk, Ubuntu 26.04,
   linger on, can reboot without warning). Tools and paths are in CONTINUE.md §0.
1. Read `CONTINUE.md` in full, starting with §0 "READ THIS FIRST" (server, tools, reading order, rules) and the
   newest HAND-OFF section (what is running, where results land, next steps). Then README.md, RESULTS.md and
   IDEAS.md in full, and follow their instructions fully.
2. Read the newest file in `context/chats/` (`context/INDEX.md` lists them): the exported conversations, including the
   last messages and commands of the previous session.
3. Check what is running **with the sandbox disabled** (the Bash sandbox has a private /tmp, so `tmux ls` in it
   always says "no server"): `systemctl --user list-units 'symsat-*'`, `pgrep -a monster`, `tmux ls`,
   `journalctl --since -12h | grep -i oom`. After a reboot no job runs: capped units are transient (only the snapshot
   timer comes back), so restart them with the exact commands in CONTINUE.md's newest hand-off.
4. Report what happened and where things stand, with evidence, before starting new work. Pasted text from other AIs
   is input to weigh, not a substitute for reading the repo.

## Rules
- **Exact only.** Never add an unproved clause; never mix unproved symmetry breaking with pattern images. A claim
  counts only when its proof checks (Lean checker, Rust reference checker, or the symmetric checker). See CONTINUE.md §2.
- **Rust only for tooling.** Generators, tests and converters are `monster <subcommand>` or `cargo test`. No Python in
  the project. Shell scripts in `scripts/` are infrastructure only (backups, wrappers).
- **Heavy or long jobs** (Lean kernel checks, big solves, overnight runs): `scripts/capped.sh NAME 40G CMD...`, which
  runs the job as its own systemd unit with a hard memory cap. Never `setsid nohup` from the session: that stays in
  the session's cgroup, and on 2026-10-26 one 64 GB Lean process OOM-killed the whole tmux session.
- Judge speed by deterministic counters (conflicts, search nodes), before and after every change. `cargo test`
  includes `tests/regression.rs` (worst-of-4-relabellings conflict ceilings for the headline results).
- Opt-in experiment switches (`MONSTER_LIBONLY`, `MONSTER_MINE`, `MONSTER_BRANCH`, ...) and their measured verdicts
  are listed in README "Experimental switches"; check there before re-trying an idea.
- Judge a change's effect on a full run with `monster ab --base REV -- glue <full-run args> --sample K` (paired, same
  task sample, verdict agreement checked, extrapolated to the full run, logged to `bench/ab.jsonl`), not with
  ad-hoc timed runs. Uncertified runs skip re-verifying a stamped library cache, so samples start in seconds.
- **GitHub rejects files over 100 MB.** snapshot.sh and the Stop hook skip such files (tested 2026-10-28); regenerable bulk
  outputs (proof files, SDP inputs) belong in .gitignore. If pushes fail, check `~/.local/state/symsat/snapshot.log` first.
- **The account usage limit kills the session and every subagent at once** (2026-10-28 00:32, nine hours lost). Keep state in
  files (CONTINUE.md, results/, RESULTS.md) as you go; never leave work only in a subagent's context; have subagents write
  their files early and commit through the hook.
- **Server lost?** CONTINUE.md §0a is the restart-from-nothing checklist; everything needed is in git (hooks config in
  `scripts/claude-settings.json`, Claude memory in `context/claude-memory/`, the running job's resume log in results/).
- **With every code change, update CONTINUE.md**, and README.md / RESULTS.md / this file when usage, numbers or rules
  change. The Stop hook blocks once if code changed and CONTINUE.md did not.

## Backups (automatic; do not disable or bypass)
- `scripts/snapshot.sh`: every file (tracked and untracked) to branch `backup/auto` on GitHub, ungated, after
  exporting the chat context to `context/chats/`. Runs every 10 minutes (`symsat-snapshot.timer`, installed by
  `scripts/install_backups.sh`) and from Claude Code hooks (after edits, before compaction, at session end).
- `scripts/autocommit_hook.sh` (Stop hook, at the end of every turn): commits everything to `main` and pushes, but
  only if `cargo build`, `cargo test` (incl. the regression gate) and, for verified/ changes, `lake build` pass.
- Hooks: `~/.claude/settings.json`. Logs and status: `~/.local/state/symsat/`. The old hourly cron is retired.
- Recover anything: `git fetch symsat backup/auto && git log symsat/backup/auto`.

## What the user wants
Highest-impact work, honest verdicts with evidence, verification first, no pointless comparisons, regular backups,
and no wasted time: read and check before building.
