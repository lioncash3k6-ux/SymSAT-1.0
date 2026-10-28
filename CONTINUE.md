# CONTINUE: how to pick this work up (for people and for Claude)

Last updated 2026-10-28 ~12:00 UTC (newest hand-off: 5-LATEST+10). Repo **`lioncash3k6-ux/SymSAT`** (private), branch `main`. (History also on branch
`monster-rust-solver` of `lioncash3k6-ux/cascade-solver`, an ancestor of SymSAT main.)

## 0. READ THIS FIRST: instructions for the next Claude session (from the user, 2026-10-26)
**Know the server you are on.** This is a single Linux VM, host `srv-7q6ax`, user `ubuntu`:
- 16 vCPUs (Intel Xeon E3-12xx v2, Ivy Bridge: AVX, no AVX2), 62 GiB RAM, 15 GiB swap, 1.3 TB disk (~3% used),
  Ubuntu 26.04.1 LTS, kernel 7.0.0-38. Linger is on, so systemd user units (`symsat-*`) keep running with nobody
  logged in. The box can reboot without warning (it did 10:50–11:08 UTC on 2026-10-26); after a reboot nothing runs.
- Tools: Rust `~/.cargo/bin/cargo`; Lean `~/.elan/bin/{lean,lake}` (verified/ project); `gh` (`/usr/local/bin/gh`,
  logged in); CSDP 6.2 `/usr/bin/csdp` (apt `coinor-csdp`, for `monster flag`); `~/deps/cadical`, `~/deps/cake_lpr`
  (reference solver and verified LRAT checker); catalogues `~/cascade-solver-ramsey-v4-algebraic/v5/catalogs`, covers
  `~/cascade-solver-ramsey-v4-algebraic/v10/covers{,_r2}` (plus `results/covers_r45/`, links and new covers).
- The Claude Bash sandbox has a private /tmp: check `systemctl --user list-units 'symsat-*'`, `pgrep -a monster`,
  `tmux ls` and `journalctl --since -12h | grep -i oom` with the sandbox **disabled**, or you will report "nothing running"
  wrongly.

**Provenance (user, 2026-10-26): SymSAT's `monster` is the only solver that runs.** The cascade repos supply DATA only
(McKay's graph catalogues in v5/catalogs, v10's gray-edge cover files) and YARDSTICKS (v10/v11 measured timings, e.g.
 v11 ~86 s per d=10 unit with CaDiCaL + cubes). Never switch engines to v11 or CaDiCaL; port a technique into `monster`
and judge it with `monster ab`. Covers can be rebuilt with `monster cover` if v10 data should not be used.

**Read the repo, then follow its instructions fully, before answering or building anything.**
1. `CLAUDE.md` (rules and start-of-session checklist), then this whole file, then `README.md`, `RESULTS.md`,
   `IDEAS.md` (including the verdict tables for ideas already tried), then the newest `context/chats/*.md`
   (`context/INDEX.md` lists them; read the last messages and commands of the previous session).
2. Check every running `symsat-*` unit and read its output (`journalctl --user -u symsat-NAME`, its results dir).
   Section 5-LATEST below lists what was running at hand-off, where its results land, and how to restart it.
3. Report what happened since, with evidence (numbers, file paths), before new work. Pasted text from other AIs is
   input to weigh against the repo, not a substitute for reading it.
4. Rules that are not optional: exact only (no unproved clause, no symmetry breaking mixed with images, a claim counts
   only when its proof checks); Rust only for tooling (`monster <subcommand>` or `cargo test`, never Python); heavy or
   long jobs only via `scripts/capped.sh NAME MEM CMD` (never `setsid nohup`); judge speed by deterministic counters and
   full-run effects by `monster ab` on the standing samples; with every code change update this file (and README /
   RESULTS / IDEAS when numbers or usage change); never word a result as more than it proves (an assumption or one
   half of a case split is not a bound).

> Backups are automatic (§4): snapshots of every file to `backup/auto` every 10 minutes and gated commits to `main` at
> the end of every turn.

## 0a. Restart from nothing (server lost): everything needed is in git (checked 2026-10-28)
1. **Clone.** Linux x86_64, 16+ cores, 64 GB. `gh auth login`, then `git clone git@github.com:lioncash3k6-ux/SymSAT.git ~/monster`
   and `git -C ~/monster remote rename origin symsat` (scripts push to the remote named `symsat`). If `main` looks behind,
   `git fetch symsat backup/auto`: that branch holds every file as of the last 10-minute snapshot (incl. the running job's logs).
2. **Tools** (versions that worked 2026-10-28): `sudo apt install build-essential jq tmux gh coinor-csdp`; Rust 1.99 via rustup
   (README "Install"); Lean via elan, toolchain pinned in `verified/lean-toolchain` (v4.35.0). Optional cross-check tools:
   `~/deps/cadical` (https://github.com/arminbiere/cadical.git) and `~/deps/cake_lpr` (https://github.com/tanyongkiam/cake_lpr.git, `make`); csdp only for `monster flag` (closed route).
3. **Data.** `git clone https://github.com/lioncash3k6-ux/cascade-solver-ramsey-v4-algebraic ~/cascade-solver-ramsey-v4-algebraic`
   (catalogues `v5/catalogs`, v10 covers). The R(4,5) covers are tracked here (`results/covers_r45`, 131 MB).
4. **Build.** `cargo build --release && cargo test --release`; `cd verified && lake build` (checker binary
   `verified/.lake/build/bin/checker`).
5. **Claude Code.** `scripts/install_backups.sh --swap 16G` (linger, snapshot timer, and it copies `scripts/claude-settings.json`
   to `~/.claude/settings.json`: the hooks). Memory: `mkdir -p ~/.claude/projects/-home-ubuntu/memory && cp context/claude-memory/*.md
   ~/.claude/projects/-home-ubuntu/memory/`. Conversations: `context/chats/`, newest first in `context/INDEX.md`.
6. **Resume the computation.** `results/overnight/d10_certified/{meta.json,tasks.jsonl}` are tracked and re-snapshotted every
   10 minutes, so the d=10 command in 5-LATEST+5 with `--resume` continues where it was (at most ~10 min lost; a line is only
   written when a unit is certified). Same for d=12 later. Lean-verified stages: `results/leanstage/d*/{summary.json,verified.jsonl}`
   are tracked; the `.slrat` proof files are not (0.3-1.5 GB each, regenerated by `monster unit-lean-stage`).
7. **Not in git, all regenerable:** `results/flag/*` SDP inputs (GB-sized, closed route), `target/`, `runs/`, the worker bundle
   (`scripts/bundle.sh`), `results/library_*.bin` caches.

## 1. What monster is
monster is an exact Ramsey solver in Rust with no dependencies. Two engine families:
- **Pattern CDCL** (`monster full`, and `monster glue --mode hybrid`):
  - CDCL on the **full, unreduced** K_N formula. No symmetry-breaking predicates are ever added.
  - Every learned clause is stored as a canonical forbidden 2-coloured pattern, and its vertex-permuted images are
    found by embedding search and propagated (symmetric learning, like SEL but over the whole of S_N).
  - A **recursive lemma library** (general rooted lemmas: a red clique of a roots and a blue clique of b roots over
    R(s-a,t-b) leaves; a+b = 1 are the stars, the default also adds books and mixed books) is proved inside F by
    assumption solves, verified, cached in `results/library_*.bin` (format `LIBRARY_MAGIC`), and imported as patterns.
  - Hybrid mode adds **catalogue cubes**. Vertex 0's red and blue neighbourhoods are fixed to isomorph-free catalogue
    graphs as assumptions. Pattern memory is shared across cubes (sound, because every lemma is implied by F alone).
- **Gluing engines** (`monster glue --mode pair|stream|unit`): per-pair CNFs from the repo's v6 `encode.py` (byte-identical),
  plus v10 gray-edge covers and the own cover builder (`monster cover`).

## 2. Ground rules (from REBUILD_PLAN.md; do not break these)
1. **Exact only.** Never add an unproved clause. Symmetry breaking that is not implied by F (satsuma, SMS, lex axioms)
   must NOT be mixed with pattern images: images of lemmas derived from non-implied clauses are unsound. The R(5,5)/R(4,5)
   "proof" repos fail exactly this way (see `audit/R55_AUDIT_REPORT.md` on branch ramsey-v4-algebraic).
2. **A claim counts only when its proof checks against the original formula.**
   - Pattern CDCL: `src/full.rs::check_symmetric` regenerates F from (s,t,N), RUP-checks lemmas, and checks image
     lines as perm(lemma).
   - Gold standard for small cases: LRAT with images expanded, checked by cake_lpr (`--lrat FILE`, then
     `~/deps/cake_lpr/cake_lpr FILE.cnf FILE`).
3. Degree-restricted runs (`--d ...`) make **stage** claims only. R(s,t) ≤ N needs every admissible degree.
4. Measure everything; record verdicts in RESULTS.md and IDEAS.md (including negatives).

## 3. Build and quick check
```bash
source ~/.cargo/env && cd ~/monster && cargo build --release && cargo test --release   # 32 tests: 26 unit + 6 regression gate
./target/release/monster full --s 4 --t 4 --n 18 --patterns --lemmas --proof      # 61 conflicts, ~0.01 s, "s VERIFIED UNSAT" (--lib lift default)
# general rooted lemmas ("books") are the default since 2026-10-26; --no-books = stars only; --lib inline = the old path (129 conflicts)
./scripts/progress.sh        # fixed suite (~3 min), appends one row to bench/progress.jsonl
```
Catalogues: `~/cascade-solver-ramsey-v4-algebraic/v5/catalogs` (public repo; or pass `--catalogs DIR`).
Covers: `~/cascade-solver-ramsey-v4-algebraic/v10/covers{,_r2}`. Checkers: `~/deps/cake_lpr`, `~/deps/cadical` (reference only).

## 4. What is running or scheduled on this box
- **Running now: see "5-LATEST. CONSOLIDATED HAND-OFF" below** (list of capped units and where their results land).
  Linger is on and the snapshot timer is active (`install_backups.sh` has run). The tmux session `work` that held the previous Claude session
  was killed at 04:29 UTC (cause in 5b'). To run Claude so a disconnect cannot stop it: `tmux new -s work`, then
  `claude --resume` inside it. tmux protects against disconnects only, not against the OOM failure in 5b'.
- `results/overnight/one_d8`, `one_d12` (one-sided R(4,5) d=8, 2 cubes; d=12, 12 cubes): **stopped at 03:14 UTC** by the
  session itself when the user narrowed the focus to #1 and #3. Neither finished a cube.
- `results/overnight/gray_d8` (48 gray cubes, started 03:06): **crashed at 03:11** with a panic at `src/glue.rs:1133`
  ("index out of bounds: the len is 2 but the index is 2"). Not fixed.
- `results/overnight/hyb_d8` (stopped): earlier pair-cube hybrid R(4,5) d=8 run (358 pairs, 1 task in 8 certified).
  Continue with `--resume` (finished tasks are skipped), as a capped unit:
  `scripts/capped.sh hyb-d8 40G ./target/release/monster glue --s 4 --t 5 --n 25 --d 8 --mode hybrid --workers 16 --chunk 2 --check-every 8 --out results/overnight/hyb_d8 --resume --quiet`
- **Backups (since 2026-10-26 ~09:50 UTC; the old hourly cron is retired, the crontab is empty):**
  - `scripts/snapshot.sh` pushes every file (tracked and untracked) to branch **`backup/auto`**, ungated, after
    exporting all Claude conversations to `context/chats/`. It never touches HEAD, the index or main. It runs from
    Claude Code hooks (after edits, debounced to 2 min; before compaction; at session start and end) and, once
    installed, from `symsat-snapshot.timer` every 10 minutes.
  - The **Stop hook** `scripts/autocommit_hook.sh` runs at the end of every Claude turn: snapshot, then a gated commit
    of everything to `main` + push. Gates: code changed ⇒ CONTINUE.md must be updated (blocks once), and
    `cargo build`, `cargo test` (incl. `tests/regression.rs`) and, for verified/ changes, `lake build` must pass.
  - Hooks are in `~/.claude/settings.json`; logs and status in `~/.local/state/symsat/`; `CLAUDE.md` (also `~/CLAUDE.md`)
    tells every new session to read this file and `context/` first. Recover anything from `symsat/backup/auto`.
  - `~/monster/scripts/install_backups.sh [--swap 16G]` has been run (linger on, 10-minute timer active, 15 GiB swap).
  - `scripts/backup.sh` (the old cron script) now only calls `snapshot.sh`, so an old crontab line cannot commit
    untested code to main again (that happened at 03:17 and 05:17).

## 5-LATEST+10. (2026-10-28 ~12:00 UTC) user: "do what's fastest and required to finish; drop wasted work; speed pass"
**Running now: `symsat-d10-lean` only** (launched 11:53 UTC): `scripts/capped.sh d10-lean 40G ./target/release/monster
unit-lean-stage --s 4 --t 5 --n 25 --d 10 --covers results/covers_r45 --gray-a 6 --gray-b 6 --out results/leanstage/d10
--workers 10 --lean-jobs 8 --batch 6 --resume --lean verified/.lake/build/bin/checker` (the launch used a frozen copy of
the checker in the session scratchpad; after a reboot use the path above, or copy the binary first if you plan to rebuild
it while the stage runs). Progress: `wc -l results/leanstage/d10/verified.jsonl` (70,669 units; `--resume` skips the
verified ones), per-batch record files in `results/leanstage/d10/rec/`, summary.json at the end (`complete: true`).
Expected ~16 days on this box (RESULTS "2026-10-28 ~11:30"); proof files are deleted after verification, in-flight
disk use < 100 GB. **`symsat-d10-certified` was stopped at 5,050 / 70,669 units (11:55)**: it kept no proofs, so every
unit it solved would have been re-solved for the Lean theorem; its `tasks.jsonl` stays as a partial certified record.
**Speed pass (RESULTS "~11:30"):** (1) `unit-lean` / `unit-lean-stage` now use cube-and-conquer exactly like the certified
unit mode (`--cube-budget`, default 5,000): conflict counts equal the certified run's, proofs halve (whole-unit solves did
~2x the conflicts); (2) byte-level `parseLineFast` in the Lean checker (parsing was 53% of a check; -31% on a lemma
check; `checker --parse FILE`); (3) the stage driver runs `--lean-jobs J` Lean processes concurrently (one record file per
batch in `DIR/rec/`; `assemble-spec --from-record DIR`); the 4-worker cap is gone. Per hard d=10 unit: 124 s solve +
89 s Lean vs 136 s certified (1.6x; was 4.7x). Closed: proof trimming (94% of lemmas are in the cone of ⊥).
**12:40 addendum:** checker now runs `rupFast` (array assignment, csimp-proved; −15-20% per check; the d=10 stage was
switched to it at 12:35 by replacing the frozen binary), `unit-lean-stage --shard I/N` exists, `scripts/bootstrap.sh`
(one command to a running Lean shard on any Debian/Ubuntu box or Termux+proot; tested here) and the bundle carries the
checker + `run_lean_shard.sh` (RESULTS "~12:40"). To add machines to d=10 now: run shards `--shard I/N` elsewhere and
restart this box's stage with its own `--shard 0/N` (units already in its verified.jsonl are skipped by `--resume`).
**13:00: SymSAT 1.0 public release** at https://github.com/lioncash3k6-ux/SymSAT-1.0 (MIT; release snapshot of `main`
without `context/`; `scripts/release.sh` re-publishes it). `monster bootstrap` / `scripts/bootstrap.sh` clone the public repo
(no credentials needed on worker machines); `monster merge-shards --out DIR SHARD...` merges shard outputs. Scalar literal
status in the checker: tried, slower, reverted (RESULTS "~12:55").
**13:10: checker −34% more** (RESULTS "~13:10"): the lemma check cost was NOT hint evaluation (0.5 s of 2.95) but a
per-step rebuild of the edge table (0.9 s, fixed in Stream.lean) and allocation churn (chunked byte reader, `getCFast`,
preallocated assignment). 20 MB proof: 2.95 → 1.95 s; this morning 6.15 s. Harness: `scripts/bench_checker.sh`; profile with
`sudo perf record` (works without sysctl). The d=10 stage runs this checker since 13:10. Idea "packed clause store" is
CLOSED: measured not the lever.
**14:40: counting route CLOSED** (user: "focus everything on this"): `monster count-kill` census, 0 of 40.9 M d=10 pairs
and 0 of 358 d=8 pairs refuted by any counting condition up to edge-level double counting (RESULTS "~14:40", IDEAS).
No order of magnitude exists there; the remaining lever is machines.
**14:25: biclique reencoding under measurement** (user: "dynamic bicliques; has to be verifiable; approval to discover"):
`glue --mode unit --biclique` (src/cover.rs `build_gamma_opts`, `Aux`): SBVA-style definition variables z = OR / r = AND of one
vertex's cross literals to a mono set on the other side turn the K(2,3)/K(1,4)/K(2,2)/K(1,3) clauses of a unit into 2-literal
clauses; uncertified (refused with `--check-every > 0`). Running: `symsat-ab-biclique` (paired 16-unit d=10 sample, results in
`results/ab/2026-10-28T142353Z`, row appended to bench/ab.jsonl) and a 2-unit probe. Verifiable design if it wins: give each
definition variable a SEMANTIC definition in the checker's variable table (`VarDef = edge a b | or lits | and lits`, one level,
lits must be edges), so the definition clauses are tautologies in every colouring and all soundness statements stay universal
(no existential invariant); only ~14 Lean sites read the table as a pair; new line `u k e z lits 0` defines z in a sub-database;
the translator maps solver aux vars to fresh ids. Verdict and next step go into RESULTS when the ab run ends.
**14:55 interim (2-unit probe, seed 7):** plain (7,971) 840k conflicts / 36 s, (10,3190) 3.76 M / 287 s; biclique 2.13 M / 312 s and
3.13 M / 647 s; + definition variables excluded from decisions (`Solver.no_decide`) 2.33 M / 428 s and 2.62 M / 493 s; blue-only
variant (`MONSTER_BICLIQUE_BLUE=1`) 3.6 M / 593 s on the second. Fewer conflicts at best, 2-9x slower: the reencoded formula is
~90% binary clauses and each conflict cost 2.5x. Added a **binary-clause fast path** to `propagate` (`Watch.bin`, no arena read;
plain formulas unchanged: identical conflicts, neutral time; 39 + 6 tests pass); the probe with it is running, as is the paired
16-unit `symsat-ab-biclique` (plain reencoding) whose row lands in bench/ab.jsonl.
**15:20: biclique route CLOSED** (RESULTS "~15:20"): all variants slower; the Lean definition-variable extension was designed,
not built; `Watch.bin` binary fast path kept (neutral, tested). Counting, symmetry inside units and bicliques are now all
measured dead at the unit level; the remaining real lever is machines.
**15:50: the 1995 decomposition, under measurement** (user: "discover what's left"): McKay–Radziszowski did NOT glue full
(3,5,d) graphs; they deleted one vertex of the neighbourhood and glued a small sparse family (53 (3,5,9)-graphs for d=10)
against every (4,4,14)-graph (r45.pdf §2-3; 3.2 CPU-years on 12-MIPS Sparcstations ≈ CPU-days today; the 2024 HOL4 proof
went back to direct gluing with covers and needed <950 CPU-days, our regime). In our framework that is just another cover:
`monster cover-mr --d D --out results/covers_mr` (src/mrcover.rs) writes A = "(3,5,d-1)-graph + one all-gray vertex" (greedy
hitting family, 52 gens for d=10, 32 for d=8) and B = every catalogue graph itself (g0); both verified by `Cover::load`. No Lean
change: gray edges are already free in the bridge. Running: `symsat-mr-d8` (all 64 units, certified, `results/ab/mr_d8`) against
the current d=8 stage's 1,057 solve CPU-s, and `symsat-mr-d10-sample` (16 of 6,802,432 units, `results/ab/mr_d10_sample`).
**16:30: 1995 interval gluing rebuilt and measured** (user: "push in the DPLL direction"): the vertex-deletion cover is 15x
worse as CDCL units; the interval DFS per pair (src/interval.rs, `monster mr-glue`) is 8x worse than CDCL (10^8 nodes at
0.16 µs; no learning); the paper's double tree + lookahead + symmetries would plausibly give 2-5x, weeks of work, proofs as
tree resolution. Biclique paired verdict: 2.53x slower. Everything measured today is in RESULTS "~14:40", "~15:20", "~16:30".
The production run `symsat-d10-lean` kept going throughout.
**Then:** d=12 Lean stage (`--d 12 --gray-a 6 --gray-b 8`, ~37,034 units; after d=10 on this box, or now on another
machine from the bundle: the stage driver needs the checker binary too, add `verified/.lake/build/bin/checker` to the
bundle); final assembly: three `assemble-spec` blocks (`--from-record results/leanstage/d8keep/verified.rec`,
`--from-record results/leanstage/d10/rec`, `--from-record results/leanstage/d12/rec`) into one spec, `checker
--assemble SPEC` → `s R(4,5) <= 25 ASSEMBLED`. Remaining Lean speed idea if needed: the check itself is now ~75% of Lean
time (RUP over `Array (Option (List Int))`); a packed clause store would be the next lever, with proof changes.

## 5-LATEST+9. (2026-10-28 ~11:30 UTC) user: "assemble it now, verify with a small proof, memory-efficient, fast": DONE
**The assembler exists and is verified on real stages.** `checker --assemble SPEC` (verified/Main.lean) +
`verified/MonsterVerified/Assemble.lean` + `monster assemble-spec` (src/assemble.rs). What was missing and is now in Lean:
the covers map catalogue graphs to generalisations only **up to a vertex permutation** (`A catidx genid t pi...`), so the
unit clauses refute relabelled graphs; `unitShape_relabel` / `stageRefuted_of_relabelled` lift that to the listed graphs.
`stageOK` is the parallel Bool check (per-graph hints = generalisation + σ = pi⁻¹, untrusted; clause table per unit);
theorems `stageRefuted_of_verified` (in-process: the assembler verifies the SLRAT files itself, **no hypothesis**) and
`stageRefuted_of_record` (clauses from `verified.rec`, written by `checker --lemmas --record`, which `unit-lean-stage` now
passes); `r45_le_25_of_stages` (d = 8, 10, 12 → R(4,5) ≤ 25 under `CatalogueComplete`). Axioms: standard three for the
stage theorems (SOUNDNESS.md "The assembler"; README; RESULTS "2026-10-28 ~11:00"; docs/ASSEMBLY.md status).
**Verified:** d=7 end to end in both forms + mutant, as `cargo test --release assemble_d7` (122 s; 39 + 6 tests pass);
five mutations at d=8 all rejected; **d=8 record form: `s STAGE 8 REFUTED GIVEN THE RECORD`** on the regenerated stage
(`results/leanstage/d8keep`, 30/30, record `verified.rec`, spec + output in `results/leanstage/assemble/`); **d=8 in-process form: `s STAGE 8 REFUTED` by `stageRefuted_of_verified`** (30 lemmas, 3.2 GB of SLRAT re-verified in one
process, 910 s, peak 135 MB, exit 0; `results/leanstage/assemble/d8_inprocess.out`): the hypothesis-free small proof. **Cost:** coverage check d=10 (40.9 M pairs) 229 s wall / 361 MB, d=12
(17.4 M pairs) 138 s / 597 MB, 14 threads (fake records = the exact unit clauses). Bug fixed: `--keep` / `--fake` were not
boolean flags (`--keep` never kept files). The d=8 proof files (3.0 GB, `results/leanstage/d8keep/units/`, gitignored)
can be deleted once the in-process run is recorded.
**Final theorem run (when d=10 and d=12 are solved and Lean-staged):** one spec with three `stage` blocks:
`monster assemble-spec --d 8 ... --from-record results/leanstage/d8keep/verified.rec --spec FINAL.spec`, same for `--d 10
--gray-a 6 --gray-b 6 --from-record results/leanstage/d10/verified.rec` and `--d 12 --gray-a 6 --gray-b 8 --from-record
results/leanstage/d12/verified.rec`, then `checker --assemble FINAL.spec` prints `s R(4,5) <= 25 ASSEMBLED` (exit 0).
The Lean stage for d=10 needs the solved units' proofs: `monster unit-lean-stage --d 10 ... --out results/leanstage/d10`
re-solves every unit with proof export (it is a separate run from `symsat-d10-certified`, which keeps no proofs); budget:
d=8 was 3.2 GB exported for 30 units, Lean 0.9x solve CPU; d=10 ≈ 70,669 units, ~1,600-3,700 CPU-h solve + ~0.9x Lean.
**Next:** (1) let `symsat-d10-certified` finish (or shard it); (2) decide whether to run `unit-lean-stage` for d=10 on
other machines in parallel with the certified run (same bundle; `--resume`; `verified.rec` per shard concatenates);
(3) d=12 solve + Lean stage; (4) final assemble.

## 5-LATEST+8. (2026-10-28 ~09:30 UTC) what happened overnight: session limit at 00:32, pushes blocked 00:22-09:22, fixed
**Session end:** at 00:32 UTC the previous session hit the account usage limit ("session limit, resets 1:20am UTC"); both
subagents died (the stage-driver agent, part 7, and the assembly agent on `checker --assemble`). Nobody restarted anything
until 09:19. No work on disk was lost: `src/leanstage.rs` + `monster unit-lean-stage` landed, and its acceptance run
finished on its own at 00:46: **d=7 (8/8 units) and d=8 (30/30 units) Lean-verified, `complete: true`, 0 failed**
(`results/leanstage/d{7,8}/summary.json`, Lean-printed clauses in `verified.jsonl`; d=8: 3.19 GB exported, Lean 990 CPU-s,
peak 136 MB, 4 batches of 8, wall 1,487 s with 3 workers). The assembly agent's unfinished `checker --assemble` driver
(Main.lean) was only in its context: nothing of it is on disk, it has to be redone (G6.lean, Bridge.lean, Assembly.lean are in).
**Pushes blocked 9 h:** the 00:30 auto-commit (0c56fbe) included six `results/leanstage/d8/units/*.slrat` proof files of
0.3-1.5 GB (the stage driver deletes them after verification, but the hook ran mid-stage). GitHub rejects blobs over 100 MB,
so the main push and every backup/auto push after 00:22 failed ("unexpected disconnect while reading sideband packet").
Fix (09:22): 0c56fbe re-created as **02de4f6** without the blobs and pushed; local backup/auto reset to GitHub's and
re-snapshotted (pushed); `.gitignore` now excludes `results/leanstage/**/*.slrat` and `results/leanstage/*/units/`;
`scripts/snapshot.sh` and `scripts/autocommit_hook.sh` now drop any file over 95 MB (tracked or untracked) before
committing (tested: a fake 100 MB file was skipped, hook dry-run ok). The old blobs are still in `.git` (unreachable
except via reflog); `git reflog expire --expire=now --all && git gc --prune=now` reclaims ~5 GB when convenient.
**Running:** `symsat-d10-certified` only (restarted 13:17 on 10-27; 4,595 / 70,669 units done at 09:25, 0 errors,
~230 units/h at 12 workers => ~12 more days). Restart command in 5-LATEST+5.
**09:45: restart-from-nothing checklist added as §0a; hooks config tracked at `scripts/claude-settings.json` (installed by install_backups.sh); Claude memory mirrored to `context/claude-memory/` by export_context.sh; README (`unit-lean-stage`, install), RESULTS (d=7/d=8 Lean stages, status table), CLAUDE.md (100 MB and usage-limit rules) updated.**
**Next:** (1) redo the `checker --assemble` driver (reads g6 files, streams unit lemmas into `hsound`, evaluates
`catalogueCoveredIdx`), per docs/ASSEMBLY.md and SOUNDNESS.md; (2) run `monster unit-lean-stage` on d=9 (certified stage;
budget the disk: d=8 exported 3.2 GB with delete-after-verify) and on d=10 when the stage completes; (3) d=12 with
`--gray-a 6 --gray-b 8` after d=10 (5-LATEST+6). Keep sessions short of the usage limit: hand work to the hook-committed
files, not to subagent context.

## 5-LATEST+7. (2026-10-27 ~23:10 UTC) user: "build SR and improve speed"; shard switch + SR rule landed
**Speed:** every solver lever is measured out; the remaining lever is more machines: `glue --shard I/N` built and
tested (README switches, RESULTS "~23:10"). To run d=10 on N machines: copy `target/release/monster`, the catalogue dir
(`--catalogs`, 57 MB) and `results/covers_r45` (143 MB); on machine I run the d=10 command of 5-LATEST+5 with
`--shard I/N --out results/overnight/d10_shardI` (no `--resume` needed the first time); bring back each
`tasks.jsonl`, concatenate into `results/overnight/d10_certified/tasks.jsonl` (the local run's lines may be included,
duplicates are harmless) and run the original command with `--resume`: it certifies completeness and writes
summary.json. Same for d=12 with `--gray-a 6 --gray-b 8`.
**Bundle for other machines (23:50): `scripts/bundle.sh OUT.tar.gz` (binary + catalogues + covers + `run_shard.sh D I N [WORKERS]`, 56 MB; a copy is at `~/symsat-bundle.tar.gz`; tested: a d=7 shard ran from the extracted bundle). Assembly plan for the final Lean theorem: `docs/ASSEMBLY.md` (parts 5a-5c for the Lean agent after part 4).**
**SR generator (23:35, src/srgen.rs, `monster sr-gen`): R(3,3), R(3,4), R(3,5), R(4,4) refuted and the K_25 degree bounds derived as checked SR lines (RESULTS "~23:35"); step (2) of the list below is DONE.**
**SR:** the reference checker now has the SR rule and tiers (RESULTS "~23:10"; format in README and `full.rs`
docs). Heule's R(4,4) <= 18 proof verifies (`monster sr-check`). **Lean SR: DONE (2026-10-28 ~00:30, Lean agent part 4; REPORT4.md in
the session scratchpad):** `verified/MonsterVerified/SR.lean` + tiers in Checker.lean (`srList`, six-part `StOK` with "some good
colouring satisfies both tiers"), hinted `r` lines (`sr_step` emits α hints + per-clause hint groups; `sr_to_slrat_hinted`,
`slrat_add_hints`, `monster slrat-hints IN OUT`); Heule's proof: hinted 1.9 MB, Lean VERIFIED UNSAT 0.9-1.7 s / 28 MB, flipped
-37 mutant rejected by both checkers; sr-gen refutations R(3,3)..R(4,4) Lean-verified (<= 1.5 s); K_25 degree bounds: hinted
70 MB, Lean checks every line in 54 s / 51 MB ("VERIFIED STEPS", SR-tier result). Axioms unchanged; 36 + 6 tests (Lean parts gated
on a probe of the binary). Step (1) of the list below is done. **Batch lemma mode: DONE (2026-10-28 ~01:30, part 6, REPORT6.md):** `checker --lemmas LIST [--delete]`
(Main.lean; `Verified` / `OKSt.verified` / `batch_sound` in Stream.lean): one process, one file's databases at a time, originals shared;
per-file VERIFIED LEMMA / NOT VERIFIED lines + `s BATCH` count, exit 0 iff none failed, `--delete` removes verified files; only pure
last clauses count. 3 d=7 units + mutant: 15-18 s, 67 MB; Rust test `unit_lean_batch_lemma_mode` (gated on the binary). Axioms
`[propext, Quot.sound]`. Next steps, in order: (1) Lean: SR rule with
soundness proof (the Lean agent, part 4; needs hinted SR lines: per clause D a RUP hint list, so `sr_step` must
also emit hints = an LSR-style line), (2) a generator of SR lines for the K_25 meta-level: sort the neighbours of
vertex 0, derive 7 <= red degree <= 13 (R(3,5) <= 14 and R(4,4) <= 18 arguments as sorting + propagation inside the
neighbourhoods), so the degree bounds stop being trusted input; (3) parity (some vertex has even degree) as a Lean
combinatorial lemma; (4) catalogue completeness as an SR enumeration proof (research). Running: `symsat-d10-certified` only.

**~01:10: part 7 in progress (SR agent): `src/leanstage.rs` + `monster unit-lean-stage` (export every unit of a gluing stage, verify in Lean batches with delete-after-verify, record the Lean-printed clauses in DIR/verified.jsonl); acceptance run on the d=7 and d=8 stages is running; the file may be committed mid-work by the hook.**
**00:55: batch lemma mode (part 6) verified (RESULTS "2026-10-28 ~00:55"): `checker --lemmas LIST [--delete]`, `batch_sound`. Remaining to connect: the assembly agent's G6 decoder + clause -> ¬UnitShape bridge (in progress), then a `monster` driver that exports units, batches them through Lean and emits the coverage list.**
**00:30: Lean SR (part 4) verified by the main session: `check_sound` axioms standard; Heule's R(4,4) proof Lean-verified in 1.07 s; K_25 degree bounds Lean-checked in 56 s (RESULTS "2026-10-28 ~00:30"). The assembly agent is on (b) a `Catalogue` from g6 files and (a) the clause -> ¬UnitShape bridge; the SR agent is next assigned the batch lemma mode (`checker --lemmas LIST`, docs/ASSEMBLY.md).**
**Lean parts 5a/5b/5c (2026-10-28, verified/MonsterVerified/{Parity,Degree,Assembly}.lean, in `lake build`, no sorry): 5a `exists_even_red_degree : ∃ v < 25, redDegree c 25 v % 2 = 0` (handshake, general odd n); 5b `red_degree_le_13` / `red_degree_ge_7` for `Good 4 5 25 c` via `good_induced` (restriction to a neighbour list) and `R35_le_14` / `R44_le_18`; 5c `r45_le_25 (cat) (hcat : CatalogueComplete cat) (hunits : UnitsRefuted cat) : ∀ c, ¬ Good 4 5 25 c` fully proved (statements of `CatalogueComplete`, `UnitShape`, `UnitsRefuted` in Assembly.lean; SOUNDNESS.md "Assembly lemmas"). Axioms: standard three, plus the `native_decide` axioms of R35_le_14 and R44_le_18 in 5b/5c. Next: generate `UnitsRefuted` from the batch lemma mode (per-unit `UnitShape` clauses), and a `Catalogue` instance from the g6 files.** **Done (2026-10-28, G6.lean + Bridge.lean, in `lake build`): `catalogueFrom texts : Catalogue` (graph6 decoder, red = edge, validated on the real files: counts match McKay, all decoded graphs good); bridge `unit_refuted_of_clause` (a sound clause whose literals the unit shape all falsifies, read through the edge table, refutes `UnitShape`; handles generalised sub-clauses), coverage checks `catalogueCovered` / `catalogueCoveredIdx` and `unitsRefuted_of_covered(Idx)`, `r45_le_25_of_covered`. Remaining gap: the `checker --assemble` driver (Main.lean) that reads the g6 files, streams the unit lemmas into `hsound` and evaluates the coverage Bool; SOUNDNESS.md "The concrete catalogue and the unit-clause bridge".**

## 5-LATEST+6. (2026-10-27 ~19:30 UTC) verdicts on options 1, 3, 5; what is running
**Option 1 (degree axioms) CLOSED:** 32x slower on the paired d=12 sample (RESULTS "~19:30"); `symsat-ab-d12-degax` was
stopped by the main session at 19:12 (no ab.jsonl row). Do not build the exact follow-up.
**Option 3 (d=12 covers) WON: use `--gray-a 6 --gray-b 8` for d=12** (`results/covers_r45/c35_12_g6.txt`, 2 generalisations
of the 12 R(3,5;12) graphs; `c44_12_g8.txt`): 37,034 units, ~2,600-2,800 CPU-h extrapolated (~7 days on 16 cores) vs
~11,500-14,100 with gray-a 0. Launch command when its turn comes (after the d=10 stage, or now if cores are free; NOT
before the K=8 nbhd SDP verdict, which could make both stages unnecessary):
`scripts/capped.sh d12-certified 40G ./target/release/monster glue --s 4 --t 5 --n 25 --route all --d 12 --mode unit
--covers results/covers_r45 --gray-a 6 --gray-b 8 --workers 12 --check-every 1 --quiet --out results/overnight/d12_certified --resume`.
The cover subagent is still working: `symsat-cover12-g10` (c44_12_g10, possibly cheaper still) and a d=10 cover
measurement (new covers c35_10_g8, c44_14_g8; 16-unit samples for (6,6), (8,6), (6,8), (8,8)); report in the session
scratchpad covers12/REPORT.md sections 1 and 4. d=10 verdict (21:30): NO win, all tested covers within noise of (6,6) (RESULTS "~21:30"); the d=10 stage stays as launched. c44_12_g10 was not built (~40 CPU-h; deferred).
**Option 5 (Lean-checked units) DONE** (part 3 verified 19:20: lake build, cargo test 31+6, d=7 unit with deletions
VERIFIED in 3.5 s / 51 MB): every d=10 unit is Lean-checkable (hardest certified unit, 6.1 GB proof, 43 min / 307 MB).
Files: verified/MonsterVerified/{Stream,Assume,Lemma,Checker,Parse}.lean, verified/Main.lean, src/{leanunit,full}.rs,
verified/SOUNDNESS.md. Not built: cube-mode proofs through `unit-lean` (would need `glue::cube` exposed).
**22:17: K=8 nbhd SDP finished: λ = -3.83e-8, NO certificate (RESULTS "22:17"); option 2 closed at K=8. Only `symsat-d10-certified` runs now (all 16 cores, affinity and CPUWeight restored); then d=12 with the new covers.**
**Running at 19:30 (historical):** `symsat-d10-certified` (1,072 / 70,669 units, 244.6 s/unit on a box at load 26; errors 0),
`symsat-flag-k8-nbhd10-13` (csdp-omp since 14:38, 13.3 CPU-h so far; the plain K=8 run needed 15.3 CPU-h; if λ > 0 and the
exact check passes, R(4,5) <= 25 follows from the certified d=7,8,9 stages + catalogue completeness and the d=10/d=12
stages are unnecessary: stop them and write it up; if λ = 0, option 2 is closed at K=8 too), `symsat-cover12-g10`,
the cover subagent's d=10 sample unit. Session waiter for the K=8 SDP: `bgtbfszbc`.

## 5-LATEST+5. (2026-10-27 ~11:45 UTC) user: build the smallest proof format, verification, fastest solves
**13:00 UTC update.** [11,13] SDP: λ = 0, NO certificate (RESULTS "12:51"): the K=8 flag route is closed. d=12 costed:
~6,300 CPU-h with cube + drop 90 (RESULTS "~12:45"). **Launched the certified d=10 stage** (required under every remaining
route): `symsat-d10-certified`, 12 workers since 13:17 UTC (8 before; + checker threads at ~20% CPU each), cube 5k, drop 90, streaming checker,
`results/overnight/d10_certified/` (70,669 units; ~1,642 CPU-h of solving, so ~4-9 days depending on how much the
checker threads cost). Restart after a reboot: `scripts/capped.sh d10-certified 40G ./target/release/monster glue --s 4
--t 5 --n 25 --route all --d 10 --mode unit --covers results/covers_r45 --gray-a 6 --gray-b 6 --workers 12 --check-every 1
--quiet --out results/overnight/d10_certified --resume`. Done when summary.json says `certified_pairs == pairs_done ==
3,116,... (plan_pairs), complete true, errors 0`. **Option 5 BUILT (14:20, by a subagent, verified by the main session): `monster unit-lean --s 4 --t 5 --n 25 --d D
--covers DIR --gray-a GA --gray-b GB --ga I --gb J OUT.slrat [--budget C] [--all-fixed] [--no-check] [--lean
verified/.lake/build/bin/checker]`** (src/leanunit.rs) exports one unit's refutation as an SLRAT proof over the full
K_25 formula; `checker --lemma` (verified/MonsterVerified/Lemma.lean, `checkLemma_sound`) verifies it in Lean and
reports the clause ¬(fixed edges). d=7 / d=8 units: Lean 18-65 s each. **Assumption rule DONE (14:30, Assume.lean; d=9 unit with 1.3M lemmas Lean-verified in 124 s / 2 GB).**
(14:45) The agent is now mid-way through part 3 (deletion lines `u k d ..` in the assumption sub-database + a streaming
parser, new file verified/MonsterVerified/Stream.lean, Checker/Parse/Main.lean, full.rs, leanunit.rs); in-progress
edits may be committed by the hook while it works. Report expected in the session scratchpad `leanunit/REPORT3.md`. Next step
assigned to the same agent: deletion lines inside the assumption sub-database + streaming parse, so the d=10 tail
becomes Lean-checkable; the practical use is Lean-checking the small stages fully and the d=10 stage by sample. RESULTS "~14:20". Stop hook runs `lake build`.
**Option 2 BUILT (14:00): catalogue-constrained flag SDP** `monster flag --nbhd LO,HI [--handshake] [--nbhd-l L]`
(src/flag.rs `Nbhd`, `build_nbhd`, extended SDPA writer and `exact_check`; test `rooted_count_identity`). Red
neighbourhoods are catalogue (s-1,t)-good graphs; rooted subgraph counts must be a convex combination of the
catalogue graphs' counts; free multipliers μ per rooted type, one SDP row per catalogue graph; certificate
condition α + β + γ > 0, checked exactly. **R(4,4) <= 18 certified at K=4 and K=5 with `--nbhd 0,8`** (plain flags
fail at both). R(4,5) N=25: K=6 with `--nbhd 7,13` and `--nbhd 10,13` (+handshake): λ ≈ 0, no certificate (CSDP
"stuck at edge of primal feasibility"). K=7 (both ranges): λ ≈ 0, no certificate (14:17). **Running: `symsat-flag-k8-nbhd10-13`** (K=8, nbhd 10..13 +
handshake, csdp-omp 12 threads, out `results/flag/R45_N25_K8_nbhd10-13/`; decisive for option 2 at K=8). A `--nbhd 7,13`
certificate would give R(4,5) <= 25 modulo catalogue completeness alone (no gluing stage at all); `--nbhd 10,13` needs
the certified d=7,8,9 stages as well.
**Degree axioms in unit mode (13:30, measurement only):** `cover::unit_degree_axioms` + `--degree-axioms` in
`run_unit_task` (refused when certifying). Paired A/B on the d=12 16-unit sample: `symsat-ab-d12-degax`
(`results/ab/r45d12_degax`, row in bench/ab.jsonl). If it wins big (>2x), the exact version needs degree bounds as
derived constraints (a PB proof system or lifted R(3,5)/R(4,4) lemmas), which is the next build; if not, closed.
**Hint checker optimised** (13:05): Fx-style integer hasher for the clause-id
map and a reused trail buffer (`src/sat/checker.rs`); 28 + 6 tests pass; CPU-time A/B on a 3-unit seed-7 sample
(`--check-every 0` vs `1`, old vs new checker): 434 / 530 / 517.5 s CPU: certification costs ~20% CPU, the hasher
change is noise (kept). RESULTS "~13:15".

**Measured first, as proposed:** (1) unit symmetry: `monster cover-aut` (new; `Gen::stabiliser`) shows the cover
generalisations are almost all asymmetric (d=10: A 13 of 17 trivial, B 4,032 of 4,157 trivial; every hard sample unit
has order 1 or 8) -> symmetric learning / SR symmetry breaking inside units is CLOSED (RESULTS "~11:40"). (2) External
engines on the unit DIMACS: cadical 2.1.3 and kissat 4.0.3 (apt) are not faster on the easy unit (9.9 s / 48 s vs
7.7 s); hard units: cadical 41.5 / 62.7 min vs monster 17.0 / 25.9 min (at drop 50); kissat unfinished at 64 min,
stopped. CLOSED: our engine is >2.4x faster on the tail (RESULTS "~11:40", final bullet). (3) Lemma transfer across units (option 2): not measured yet; the structural argument (the B-free
sub-formula is just per-vertex cone constraints, the hardness is in the mixed clauses) makes it unlikely to pay.
**Built:** online LRAT checking with deletions in unit mode (RESULTS "~11:40"): `LratLine::Delete`, `Solver::lrat_sink`
+ `lrat_flush` / `lrat_finish`, `HintChecker::delete` / `live`, checker thread in `run_unit_task`, `certify_unit` takes
the joined checker. 28 + 6 tests pass. End-to-end check of the d=7,8 stages with the streaming checker: 429 pairs, 429 certified,
errors 0, peak RSS 87 MB for 3 workers (scratchpad run, 12:02 UTC).
**Still running:** `symsat-flag-omp-deg11-13` (decisive for the route; iteration 29 at 12:23); `symsat-d12-sample16`
(DONE 12:43 UTC: 1,636.5 unit-seconds for the 16 units vs 7,768.6 whole-unit = 4.75x; d=12 stage ~6,300 CPU-h
~16 days on 16 cores; parity route total ~21 days; RESULTS "~12:45"). Restart after a reboot: `scripts/capped.sh d12-sample16 30G
./target/release/monster glue --s 4 --t 5 --n 25 --route all --d 12 --mode unit --covers results/covers_r45 --gray-a 0
--gray-b 8 --workers 3 --check-every 0 --sample 16 --seed 1 --quiet --out results/overnight/d12_sample16` (fresh dir). **Next:** read those; measure the d=12 stage with current defaults (`glue --d 12 --mode unit --sample 16 --seed 1
--check-every 0`, uncertified, extrapolate) so the parity-route total is known; then decide between (a) d=10 only (if
[11,13] certifies), (b) d=10 + d=12.

## 5-LATEST+4. (2026-10-27 ~05:30 UTC) d=7,8,9 run complete; cube adopted; certified-count fix; re-certifying 214 units
**Done:** `results/overnight/mindeg_d789/summary.json` = `complete:true, errors:0`, 1,625 units, 186,029 pairs, all
UNSAT (finished 04:02 UTC, 10.6 CPU-h in that process). Cube A/B row landed: secs 0.268 (CI 0.196-0.434), conflicts
0.529 (0.435-0.715) -> **unit mode now defaults to `--unit-budget 5000 --cube-budget 5000`** (src/main.rs; other modes
keep 20000/0; `--cube-budget 0` = whole-unit CDCL). Reduce drop 90 stays the unit-mode default. Both rows in bench/ab.jsonl.
**Gap found:** summary said `certified_pairs 85477`: (a) pairs skipped by `--resume` were never counted as certified;
(b) a task line's `checked:true` meant "check requested", not "check passed" (a failure went to the errors list, and
the seeded `symsat-d9-certified` process was stopped before writing a summary, so its 214 units / 100,552 pairs have
no written certification outcome). **Fixed in src/glue.rs:** task line `checked` = outcome (false if the errors list
grew during the task); `read_done` returns the flag; a certified `--resume` (check-every > 0) re-runs lines not
`checked:true` and counts certified skipped pairs (`pre_checked` -> `stage_checked`), so a resumed run's
`certified_pairs` covers the whole directory. 27 + 6 tests pass.
**DONE 05:32 UTC: `results/overnight/mindeg_d789_recert9/summary.json` = `certified_pairs 186029, pairs_done 186029,
complete true, errors 0` (1 h 29 min CPU, 11 min wall). The gluing half (degrees 7, 8, 9) is certified end to end.**
**Was running (finished):**
- `symsat-symsat-mindeg-recert9` (capped.sh doubled the prefix; harmless): re-certified the 214 early d=9 units in
  `results/overnight/mindeg_d789_recert9` (tasks.jsonl seeded with the 1,411 lines the combined process wrote,
  `--resume`, 8 workers, cube 5k, check-every 1; ~2 CPU-h). **Done when its summary.json says
  `certified_pairs 186029, pairs_done 186029, complete true, errors 0`.** Then record in RESULTS.md ("gluing half
  certified end to end") and README's R(4,5) row. Restart after a reboot: `scripts/capped.sh mindeg-recert9 40G
  ./target/release/monster glue --s 4 --t 5 --n 25 --route all --d 7,8,9 --mode unit --covers results/covers_r45
  --gray-a 6 --gray-b 6 --workers 8 --check-every 1 --quiet --out results/overnight/mindeg_d789_recert9 --resume`
  (cube 5k is now the default; the resume re-runs only lines without `checked:true`).
- `symsat-flag-r45-k8` (plain K=8) FINISHED 05:20 UTC: **no certificate**, λ = -3.3e-8 (zero to precision), CSDP 15.5 h
  single-threaded, 5 GB (`results/flag/R45_N25_K8/csdp.log`). Expected: K=7 only gave <= 28.
- Still running: `symsat-flag-k8-deg10-13` (decisive) and `symsat-flag-k8-deg11-13` (fallback), one CSDP core each,
  silent until done (started 01:12 UTC; same problem size as the plain one, so expect ~16 h, i.e. ~17:00 UTC).
  Journals carry the verdict (`journalctl --user -u symsat-flag-k8-deg10-13`).
- **09:10 UTC, speed-up of the SDP (user: "go"):** installed `libopenblas0-openmp` + `-dev` + `liblapack-dev` (sudo apt);
  the BLAS/LAPACK alternatives now point to `/usr/lib/x86_64-linux-gnu/openblas-openmp/` (the two running csdp processes
  keep the reference BLAS they loaded; new ones get OpenBLAS). Launched `symsat-flag-fast-deg10-13`: stock `/usr/bin/csdp`
  with `OMP_NUM_THREADS=12` on a hard link of the [10,13] input in `results/flag/R45_N25_K8_deg10-13_parity_fast/`
  (writes `problem.sol` there). To check its answer exactly: `monster flag --s 4 --t 5 --n 25 --k 8 --degree 10,13
  --parity --threads 8 --reuse-sol --out results/flag/R45_N25_K8_deg10-13_parity_fast` (regenerates the input, sees it
  is byte-identical, skips CSDP, runs the exact integer certificate check). Building CSDP from the Coin-OR source with
  OpenMP (parallel Schur-complement assembly, the real win) was blocked by the Claude Code classifier ("code from
  external"); the source sits in the session scratchpad only. The plain K=8 run did 34 iterations at ~20 min each.
  **09:40 result: OpenBLAS with 12 OpenMP threads is SLOWER** (30 min, 3 CPU-h, iteration 1 not reached; the old build
  does one in 20 min): CSDP calls BLAS on hundreds of 45-64-sized blocks, and OpenBLAS thread overhead dominates.
  Stopped; relaunched as `symsat-flag-fast1-deg10-13` with `OMP_NUM_THREADS=1` (kernel gain only). If its iteration
  time is not clearly under 20 min, stop it (`systemctl --user stop symsat-flag-fast1-deg10-13`) and let the original
  jobs finish; the only real speed-up left is the OpenMP CSDP build (needs the classifier permission or a manual make).
  **09:47 (user approved the build):** `~/opt/bin/csdp-omp` = Coin-OR Csdp master built with `-fopenmp -DUSEOPENMP
  -DSETNUMTHREADS -O3 -march=native`, linked to OpenBLAS (sanity: test/theta1 = 23.0, DIMACS errors ~1e-10). Launched
  `symsat-flag-omp-deg10-13`: `OMP_NUM_THREADS=12 OPENBLAS_NUM_THREADS=1 csdp-omp` on a hard link of the [10,13] input in
  `results/flag/R45_N25_K8_deg10-13_parity_omp/` (sol lands there; exact check = `monster flag ... --reuse-sol --out` that dir).
  Compare its iteration time (journal) with 20 min; stop the losers among {original, fast1, omp}.
  **09:54 measured: csdp-omp 12 threads = 3.2 min/iteration (6.3x); OpenBLAS single-thread = 12.6 min (1.6x, stopped);
  reference build = 20 min.** Expect the omp run to finish ~11:40 UTC (34 iterations); the originals stay as insurance
  (2 cores). When `symsat-flag-omp-deg10-13` ends: read its journal for the CSDP status, then run the exact check:
  `scripts/capped.sh flag-check-deg10-13 40G ./target/release/monster flag --s 4 --t 5 --n 25 --k 8 --degree 10,13
  --parity --threads 8 --reuse-sol --out results/flag/R45_N25_K8_deg10-13_parity_omp` (35 min set-up, byte-identical
  input, CSDP skipped, integer certificate check). For future SDPs pass `--csdp /home/ubuntu/opt/bin/csdp-omp` with
  `OMP_NUM_THREADS=12 OPENBLAS_NUM_THREADS=1` in the environment.
  **10:02 (user: "drop other tasks other than openmp"):** stopped `symsat-flag-k8-deg10-13` and `symsat-flag-k8-deg11-13`
  (8.2 h of single-thread CSDP each, no solution written; their inputs stay in `results/flag/R45_N25_K8_deg1{0,1}-13_parity/`).
  Only `symsat-flag-omp-deg10-13` runs now (6 iterations at 10:02). If [10,13] fails, the [11,13] fallback is
  `scripts/capped.sh flag-omp-deg11-13 20G /usr/bin/env OMP_NUM_THREADS=12 OPENBLAS_NUM_THREADS=1 stdbuf -oL
  /home/ubuntu/opt/bin/csdp-omp results/flag/R45_N25_K8_deg11-13_parity/problem.dat-s
  results/flag/R45_N25_K8_deg11-13_parity/problem.sol` followed by `monster flag ... --degree 11,13 --parity --reuse-sol`.
  **10:52 VERDICT [10,13]: NO certificate.** csdp-omp converged in 39 iterations / 65.5 min wall (DIMACS errors
  <= 3.5e-9), primal objective -3.4e-9, dual -2.7e-13: λ = 0 to precision, same as plain K=8. Exact check not run
  (nothing to round). Solution: `results/flag/R45_N25_K8_deg10-13_parity_omp/problem.sol`. Details in RESULTS.md
  ("~10:55"). **Running:** `symsat-flag-omp-deg11-13` (fallback, same binary, ~1 h; λ[11,13] >= 0 could be positive).
  **Why [11,13] is now the decisive run:** the d=7,8,9 stages enumerate every catalogue pair (route `all` only picks
  the degree list; no min-degree filter), so they prove "no good colouring has a vertex of red degree 7, 8 or 9".
  "All degrees in [11,13]" is therefore the same assumption as "no vertex of degree 10" given those stages. If the SDP
  refutes it: every good colouring has a vertex of red degree 10, and **the certified d=10 stage alone (70,669 units,
  ~1,642 CPU-h = ~4.3 days on 16 cores with cube + drop 90) finishes R(4,5) <= 25**, with dependency list: McKay
  catalogue completeness for d = 7, 8, 9, 10; flag coefficient code + class enumeration; everything else checked.
  If not: parity route (even-degree vertex exists; d=8 done) = d=10 + d=12 stages (d=12: 222,204 units, no cube/drop
  A/B yet; old estimate 78 days single-thread-equivalent before the 8x), or stronger flags (K=9 is far larger).
**Next:** (1) done (recert recorded in RESULTS/README); (2) flag verdicts: [10,13] certifies -> the route is complete, write
the dependency list (catalogue completeness d=7,8,9; flag coefficient code + class enumeration; everything else
independently checked) into RESULTS and README; only [11,13] -> delta=10 remains (a d=10 certified run is ~1,642 CPU-h
with cube + drop 90; stream proofs to disk first, 17M-conflict units hold ~4 GB LRAT per worker); neither -> parity
route stands. (3) Nothing else is running by user decision ("only what is required").

## 5-LATEST+3. (2026-10-27 ~02:25 UTC) jobs trimmed to what the route needs; one combined gluing run; reduce knob
**User decision: run only what is required.** Stopped: `symsat-d8-certified` (hybrid; its 357 certified verdicts stay in
`results/overnight/d8_certified`, the stage is redone below), `symsat-trace-u8` (rate-decay curve recorded in
RESULTS.md), `symsat-d9-certified` (replaced). **Running now:**
- `symsat-mindeg-d789`: the gluing half of the minimum-degree route as ONE certified run, stages d = 7, 8, 9, unit mode
  with own covers (`results/covers_r45/c35_{7,8,9}_g6.txt`, `c44_{17,16,15}_g6.txt`), cube 5k, 6 workers, every unit
  checked by the hint checker, seeded with the 214 d=9 units already done (`--resume`). Output
  `results/overnight/mindeg_d789/{tasks.jsonl,summary.json}`; done when summary says `complete:true, errors:0` with
  8 + 30 + 1,587 = 1,625 units. Restart after a reboot: `scripts/capped.sh mindeg-d789 30G ./target/release/monster glue
  --s 4 --t 5 --n 25 --route all --d 7,8,9 --mode unit --covers results/covers_r45 --gray-a 6 --gray-b 6 --workers 6
  --check-every 1 --unit-budget 5000 --cube-budget 5000 --quiet --out results/overnight/mindeg_d789 --resume`.
- `symsat-flag-k8-deg10-13` (decisive), `symsat-flag-k8-deg11-13` (fallback), `symsat-flag-r45-k8` (plain K=8; a
  certificate there would need no catalogue at all). One core each, CSDP, no progress output; read their journals.
- `symsat-ab-d10-cube5k` (finishing: 2 slow base units) and `symsat-ab-d10-drop90` (cube 5k with
  `MONSTER_REDUCE_DROP=90` vs 50, 2+2 workers, `results/ab/r45d10_drop90`). Rows -> bench/ab.jsonl.
**Reduce drop 90% ADOPTED for unit mode (03:15 UTC):** paired 16-unit row secs ratio 0.554 (CI 0.493-0.624), conflicts
1.054 (0.945-1.157): 1.8x at equal conflicts. `Solver::reduce_drop` (default 50 = the old behaviour everywhere else;
`run_unit_task` sets 90 unless `MONSTER_REDUCE_DROP` is given). Probes on the hard unit: 95% 82 s, 98% 104 s, 100%
178 s vs 90% 90 s, so 90 stays. The combined d=7,8,9 run started before this and uses 50 (it is nearly done; leave it).
Pair mode, hybrid and `full` are unmeasured for this knob and keep 50.
**Next:** (1) flag verdicts; (2) `mindeg_d789/summary.json` complete; (3) both ab rows -> set unit-mode defaults
(`--unit-budget 5000 --cube-budget 5000`, reduce drop) if they win; (4) write the route's dependency list into RESULTS
(catalogue completeness for d = 7, 8, 9; flag coefficients and class enumeration; everything else checked).

## 5-LATEST+2. (2026-10-27 ~02:00 UTC) THE MIN-DEGREE ROUTE, hinted certification, what is running now
**The route being pursued (user: "take the highest-gain route").** Let v be a vertex of minimum red degree δ in a
(4,5)-good colouring of K25. δ >= 7 (blue neighbourhood (4,4)-good, so <= 17 vertices). If δ <= 9, the gluing stage
d = δ refutes it (stage results need no minimum-degree constraint, so the existing stages count). If δ >= 10, every red
degree lies in [10,13]: a pure flag statement, which `monster flag --degree 10,13` tests (an assumption-form run; its
certificate covers exactly this case). So **R(4,5) <= 25 ⟸ stages d = 7, 8, 9 certified + a K=8 flag certificate for
degrees [10,13]**, and the d=10 / d=12 stages (145 days) are not needed. Status:
- d=7: **done, 71/71 UNSAT, all certified** (`results/overnight/d7_certified`).
- d=8: 357/358 certified (`symsat-d8-certified` still on task 268, hybrid, 40+ CPU-h on that pair). If it does not
  finish, rerun task 268 alone in pair mode (`--mode pair --check-every 1`, pairs cost ~4 s there) and merge.
- d=9: **running**, `symsat-d9-certified` (unit mode, own covers `results/covers_r45/c35_9_g6.txt` 23 gens and
  `c44_15_g6.txt` 69 gens, 1,587 units, cube 5k, 4 workers, every unit certified) -> `results/overnight/d9_certified/`;
  ~70 s per unit so far (~8 h if no tail). Resume: same command with `--resume` (CONTINUE 5-LATEST+1 style:
  `scripts/capped.sh d9-certified 30G ./target/release/monster glue --s 4 --t 5 --n 25 --route all --d 9 --mode unit
  --covers results/covers_r45 --gray-a 6 --gray-b 6 --workers 4 --check-every 1 --unit-budget 5000 --cube-budget 5000
  --quiet --out results/overnight/d9_certified --resume`).
- flags: **running** `symsat-flag-k8-deg10-13` (K=8, `--degree 10,13 --parity`, set-up 2,024 s on 4 threads, CSDP since
  ~01:47) -> `results/flag/R45_N25_K8_deg10-13_parity/`; `symsat-flag-k8-deg11-13` (the weaker case, same set-up) ->
  `results/flag/R45_N25_K8_deg11-13_parity/`; and the plain K=8 run `symsat-flag-r45-k8` (CSDP since 18:07 yesterday).
  Each prints "certificate VERIFIED ... UNDER THE ASSUMPTION that every red degree lies in [10,13]" or "no certificate";
  read with `journalctl --user -u symsat-flag-k8-deg10-13`. If [10,13] certifies, the route closes once d=9 finishes
  and d=8's last pair is in. If only [11,13] certifies, the remaining case is δ = 10 (the d=10 stage, with every degree
  >= 10 available as an extra, sound constraint). If neither, K=8 cannot do it and the parity route stands.
**Certification is no longer the bottleneck.** Pair and unit modes now log LRAT with hints and use the independent
`HintChecker` (linear): unit 13 certified in 9.7 s instead of 546 s (RESULTS.md). The old hint-free `check_log`
remains for tests; stream and hybrid modes are unchanged (symmetric checker / RUP). Vivification is disabled under LRAT
(no LRAT logging for it; it measured neutral anyway). A bug in `analyze_final` (core of a root-false assumption logged
without hints) was found by the checker and fixed; 33 tests pass.
**Other changes:** failed-literal learning in `lookahead_pick` (sound, rare: 0-4 per unit, no lever); tasks.jsonl
carries `lits` (learnt literals) and `failed`; `--resume` no longer double-counts skipped pairs in the target.
**A/B rows:** vivify neutral (ratio 1.03, CI 0.93-1.14; off). The cube-5k-vs-whole row lands in bench/ab.jsonl when the
base side's two slow units finish (`results/ab/r45d10_cube5k`); the cand side needed 5,544 s for all 16 units.
**Next:** (1) read the flag verdicts; (2) when d=9 finishes, check `summary.json` says 1,587 units certified and record
the stage in RESULTS.md; (3) finish d=8 task 268; (4) if [10,13] certifies: write up the route (RESULTS, README table)
with the exact dependencies (catalogue completeness for d = 7, 8, 9, covers checked per pair, flag coefficients /
class enumeration as in RESULTS "Trust"); (5) stream proofs to disk before any certified d=10 run (17M-conflict units
hold ~4 GB of LRAT lines in memory per worker).

## 5-LATEST+1. SESSION 2026-10-27 00:25 UTC onwards: no reboot happened; solver review; cube-and-conquer measured
**State found at 00:28 UTC (sandbox disabled):** the box had NOT rebooted (uptime 13 h), so both capped units were
still running: `symsat-d8-certified` at 357/358 (task 268, the slow tail pair, running alone since ~22:58; 32 CPU-h so
far) and `symsat-flag-r45-k8` (set-up finished 18:07 after 15,745 s single-threaded, CSDP since, 10.7 CPU-h, 5.2 GB;
no checkpoint). Snapshot timer active, no OOM in 12 h. Nothing needed restarting.

**Review of the solver (details and tables in RESULTS.md, "2026-10-27: where d=10 unit time goes"):**
- A d=10 A6B6 unit is a tiny formula: 147-152 variables, ~4,500-4,950 clauses of average length 5.7-5.9 (`monster
  gamma`), yet the hard units need 17M conflicts. The conflict rate falls with the conflict count: 17k/s on the 0.68M-
  conflict unit (1,28) (idle box, 1 worker), 6.8k/s on the 2.6M-conflict unit (7,2559), ~2.5-4k/s on the 17M-conflict
  units (12 and 15 of the sample). So the heavy tail is paid twice: more conflicts AND slower conflicts (learnt-clause
  database growth; `reduce_db` keeps LBD <= 2 forever, LBD <= 6 while used, and drops only half of the rest).
- One-unit probes of the opt-in switches that were never A/B'd (deterministic conflicts; idle box, `--workers 1`):
  cube-and-conquer (`--unit-budget B --cube-budget B`, lookahead splits inside one solver) is the only clear win:
  unit (1,28) 684k conflicts / 40.2 s -> 441k / 20.1 s at B = 5k (2k: 470k / 22.4 s; 1k: 564k / 29.3 s; 20k: 550k /
  24.6 s; 50k: 567k / 28.4 s; 100k: 635k / 33.0 s); unit (7,2559) 2.64M / 386 s -> 1.84M / 166 s at B = 20k; unit
  (13,3857) 255k / 9.9 s -> 227k / 7.8 s at 5k. `--stable` is negative on both units (631k/37 s on (1,28), 2.92M/496 s
  on (7,2559)); `--vivify` is mixed (583k/32.8 s on (1,28), 2.92M/548 s on (7,2559)). Early A/B rows show cubing is not
  uniformly better per unit (unit 4: 1.53M vs 1.11M), so only the paired sample decides.
- The tail is not solver variance: `MONSTER_PHASE_SEED=S` (new opt-in, random initial phases in unit mode) moves unit
  (1,28) between 577k and 684k conflicts and unit (13,3857) between 241k and 255k (~15%), against the 150x spread
  between units. So a per-unit seed portfolio would not pay; cubing the hard units or cheaper conflicts would.
- Code change this session: `monster flag` set-up now runs on all cores (`--threads N`; `par_map` in src/flag.rs; the
  K=8 set-up was 4.4 h single-threaded) and `--reuse-sol` reuses a finished `problem.sol` in `--out` when the SDP input
  is byte-identical (CSDP keeps no checkpoint). Tested: R(4,4)/K18 K=6 and R(3,5)/K14 K=6 certificates still verify,
  the reuse path reuses, a changed instance does not. Default behaviour otherwise unchanged.

**Running now (started 00:36-00:39 UTC, read these first):**
- `symsat-ab-d10-cube5k`: `monster ab`, the standing 16-unit d=10 sample (seed 1), base = whole-unit CDCL
  (`--unit-budget MAX`) vs cand = `--unit-budget 5000 --cube-budget 5000`, 3+3 workers. Output
  `results/ab/r45d10_cube5k/{base,cand}/tasks.jsonl`, one row in `bench/ab.jsonl` when both finish (~2-3 h: units 12
  and 15 take ~2 h each single-threaded). Verdict rule: adopt cubing as the unit-mode default only if the secs ratio's
  95% CI is below 1 (then re-estimate the d=10 and d=12 stages).
- `symsat-ab-d10-cube5k-viv`: same sample, base = cube 5k vs cand = cube 5k + `--vivify`. Output
  `results/ab/r45d10_cube5k_vivify/`, row in `bench/ab.jsonl`.
- `symsat-trace-u8`: unit (8,1487) (17.3M conflicts, 6,913 s in the sample) alone with the live dashboard captured by
  `script` into the session scratchpad `/tmp/claude-1000/-home-ubuntu/70add9c9-a2c9-4439-8e43-fa140775295e/scratchpad/trace_u8.typescript`
  (the "N conflicts/s" field over time = the conflict-rate decay curve; `grep -a -o ".\{80\}conflicts/s"`). Results dir
  `.../scratchpad/trace_u8`. Record the curve in RESULTS.md, then delete the typescript.
- Still: `symsat-d8-certified` (task 268) and `symsat-flag-r45-k8` (CSDP).

**Next, in order:** (1) read the two ab rows; if cubing wins, make it the unit-mode default (`--unit-budget` /
`--cube-budget` defaults) and re-run the d=12 sample with it; (2) a reduce-policy experiment aimed at the rate decay
(opt-in env knob: drop 75% instead of 50%, or Kissat-style sqrt-growing reduce interval), judged by `monster ab` on
the same sample; (3) when the K=8 CSDP finishes: if λ <= 0, rerun K=8 WITH `--degree auto --parity` (set-up now ~20
min on 16 cores) and the `--exclude-degree 8,10` half case, which would remove the d=12 stage if certified; (4) the
rest of the 5-LATEST list below (library-only as hybrid default, offline mining, flags for graph Ramsey numbers).

## 5-LATEST. RESTART HAND-OFF (2026-10-27 ~00:15 UTC) -- the restart did not happen; see 5-LATEST+1 above
**The user restarted the server right after this was written.** Transient `symsat-*` job units (everything started
with `scripts/capped.sh`) do not survive a reboot; the snapshot timer does (it is installed, linger is on). Everything
was committed and pushed first (`main`, and `backup/auto` with the chat export in `context/chats/`).
**After the restart, from `~/monster`:**
1. Run Claude inside tmux, so a disconnect cannot stop it: `tmux new -As work`, then `claude --resume` (or `claude -c`).
2. Check with the sandbox disabled: `systemctl --user list-units 'symsat-*'` (expect only `symsat-snapshot.timer`),
   `pgrep -a monster` (expect nothing), `git status` (expect clean), `tail -3 ~/.local/state/symsat/snapshot.log`.
3. Restart what the reboot ended (both as capped units; run from `~/monster`, `capped.sh` uses the current directory):
   - **Certified d=8**: 357/358 pairs done, all UNSAT and proof-checked; only task 268 (a slow tail, it had run alone
     for more than an hour) is left. `--resume` skips every finished task:
     `scripts/capped.sh d8-certified 40G ./target/release/monster glue --s 4 --t 5 --n 25 --d 8 --mode hybrid --check-every 1 --workers 4 --chunk 1 --quiet --out results/overnight/d8_certified --resume`
     At 358/358 UNSAT with every task checked, the d=8 stage is done (a stage result only: d=10 and d=12 remain).
   - **K=8 flag SDP** for R(4,5) N=25: lost (~5 h of set-up plus ~6 h of CSDP, roughly 18 iterations of the 30-60 CSDP
     usually needs; `monster flag` keeps no checkpoint and rebuilds the 1 GB SDP). Restart only if the user wants it
     (another ~12-25 h): `scripts/capped.sh flag-r45-k8 40G ./target/release/monster flag --s 4 --t 5 --n 25 --k 8 --out results/flag/R45_N25_K8`.
     CSDP runs on one core with the reference BLAS here; OpenBLAS (`sudo apt install libopenblas0-pthread`, the user's
     call) may help. Worth doing first: make `monster flag` save its set-up so a restart costs only the CSDP part.
**State of R(4,5) <= 25: not proved.** Two routes, both measured on 2026-10-26:
- Gluing (parity route, stages d = 8, 10, 12; uncertified unless noted): d=8 358 pairs, library-only hybrid ~4.7 CPU-h,
  certified run 357/358 at the restart (all UNSAT, every task proof-checked); d=10 70,669 A6B6 units, unit mode 1,316 s/unit on
  a 16-unit sample (~67 days on 16 cores, heavy tail); d=12 222,204 units (cover built today, `results/covers_r45/`),
  485 s/unit (~78 days). So ~4-5 months of this box: the bottleneck is per-unit cost at d=10 and d=12.
- Flag SDP (`monster flag`, exact certificates): tight R(3,3), R(3,4), R(3,5), R(4,4), R(3,6); R(4,5) <= 28 at K=7;
  nothing at K=7 settles N=25 (degrees, parity, case splits); refutes the min-degree case [12,13]. K=8 SDP: ended by
  the restart before CSDP finished (see above).
**Engines and switches** (all opt-in except where noted; full list in README "Experimental switches"):
- Defaults: the domain-based embedding search (5x on hybrid R(3,7), 3.1x on d=8) and library mode `--lib lift`.
- `MONSTER_LIBONLY=1`: only library lemmas as patterns in main/cube solvers -- **5.9x faster on the d=8 hybrid
  sample**, worse on small full formulas. Candidate default for hybrid runs.
- `MONSTER_MINE=k,budget,tries,every`: lemma mining (16x on library-free R(3,5)/K14, 50x worse on R(4,4)/K18).
- `MONSTER_BRANCH=vertex`: vertex-major decisions (36x on R(3,6)/K17, far worse on R(4,4)/K17): portfolio candidate.
- Measured negative or neutral today: node throttle, vertex vivification (BCP), book axioms as CNF, incremental
  matching (memo, global candidates), hybrid on d=10 units (even library-only: 5.8x slower than unit mode over 8
  units, 2.0-13.4x each), d=10 with the small side free (past its break-even), R(3,6)/K18 as one formula with
  library-only patterns (not solved in 1 h, with or without vertex branching). Details: RESULTS.md "22:47 rows".
- Measured negative on 2026-10-26/27 night: the feasible-cone engine (`glue --mode cone`, >= 175x slower than CDCL on
  a d=8 pair) and cone reasoning inside CDCL (`MONSTER_CONEPROP`, -11% conflicts on d=10 pairs, 2-8x slower). Details:
  RESULTS.md "Feasible-cone engine prototype"; section 5a''''''''''''''' below.
**Stopped before the restart (questions answered):** `symsat-d10-hybrid-libonly` and `symsat-d10-allgrayA` at 22:47
(user approved); `symsat-r36k18-libonly{,-vertex}` ended at 19:09 on their 1 h timeout.
**Next, in order:** (1) restart the jobs above and read the d=8 result; (2) cut d=10 / d=12 unit cost inside monster's
unit mode, where the time goes: on the 16-unit d=10 sample (results/ab/r45d10_unit_vs_hybrid/base) units 12 and 15
take 13,548 of 21,058 s (64%). Unit mode already has lookahead cubing (`--cube-budget`, IDEAS.md: its A/B was never
finished): measure it with `monster ab` on that sample first. On v11's own 24 units monster needs 1.72x v11's
conflicts (RESULTS.md, "Fixed 24-unit d=10 benchmark"), so v11-style cubes are worth ~1.7x, not an order of magnitude;
also choose covers by predicted cost; (3) make library-only the hybrid default (the d=8 row held: time ratio 0.169,
CI 0.147-0.207; hybrid is only used at d=8); (4) offline lemma mining for K25, cached with the library; (5) flags for
graph Ramsey numbers (most likely route to a new result); (6) `monster flag`: save the set-up to disk, try OpenBLAS.

## 5a'''''''''''''''. UPDATE (2026-10-27 ~00:00 UTC): cone reasoning inside CDCL, measured negative; cone engine closed
- New code: `cone::ConeProp` (per b the cones that agree with b's assigned cross edges, inside b's degree window,
  filtered by one-hop support from every other b with an assigned edge; empty domain = conflict, unanimous domain =
  implied cross edge; each returned as a clause over the assigned edges of the vertices involved, greedily minimised:
  contributors first, then single edges). Solver hook `Solver::cones` + `cone_round` (same path as `pattern_round`:
  `add_clause_mid_search`; asserts no proof logging; an empty clause sets root_unsat). Pair mode attaches it with
  `MONSTER_CONEPROP=1` (`=nodeg` without degree windows); `glue::build` refuses it with `--check-every > 0`; in pair
  mode's tasks.jsonl `nodes` / `embed` then carry the propagator's implied edges / conflicts. `monster cone --cdcl`
  compares plain CDCL, CDCL+cones and CDCL+cones-nodeg on single pairs (`cone::cdcl_pair`). Test: the CDCL cross-check
  now also runs CDCL+cones (both settings) on the 160 random pairs and checks verdicts and models.
- **Results (RESULTS.md, "Feasible-cone engine prototype"): negative everywhere.** Standalone cone search on the d=8
  pair: 390 s (forward checking), 562 s (+degree windows), > 549-600 s with arc consistency, against 2.2 s for plain
  CDCL. Cone propagator inside CDCL: -17% conflicts on that pair, -11% over four d=10 pairs (-45% to +10%), 2-8x slower.
  The engine and the propagator stay as opt-in switches; nothing else changes.
- The seventh paste ("polynomial routes": book algorithm, derandomisation, explicit Ramsey graphs, theta, FPT) has
  nothing for an exact upper bound beyond what is already used (IDEAS.md). Next steps: unchanged (5-LATEST list).

## 5a''''''''''''''. UPDATE (2026-10-26 ~23:30 UTC): feasible-cone engine prototype (user-approved test, IDEAS.md)
- New code: `src/cone.rs` (cone tables per A: feasible cones, red/blue compatibility bit matrices, clique numbers of
  all subsets; search with bitset domains, forward checking, smallest domain first; options `Opts { degrees, mac }`:
  degree windows from R(s-1,t) and R(s,t-1) via McKay's table, maintained arc consistency). `glue --mode cone`
  (tasks are units with `--covers`, else pair chunks; refuses `--check-every > 0`: no proofs; SAT answers are rebuilt
  and brute-force checked like every other mode; options from `MONSTER_CONE=deg,mac`, default both), and
  `monster cone --s S --t T --n N --d D --a I,.. --b K,.. [--opts deg+mac,deg,mac,none] [--secs X]` for single pairs.
  `glue::uses_covers` replaces four copies of the cover-mode condition. Tests: `cone::tests` (brute force on 419 small
  pairs, CDCL pair encoding on 160 random larger pairs with both verdicts, R(3,3) and R(3,4) by gluing; every option set).
- **First measurement (forward checking only): negative.** R(4,5) d=8 pair A#136 x B#0: UNSAT, 529M nodes, 390 s.
  Pair-mode CDCL does a d=8 pair in ~4 s (RESULTS.md), so ~100x slower. Measuring `deg`, `mac`, `deg+mac` on the same
  pair next (`monster cone ... --a 136 --b 0`); kill criterion: drop the engine unless it beats CDCL by >= 10x per pair
  (d=8 ~4 s, d=10 units ~1.2-2.3 s per pair).

## 5a'''''''''''''. UPDATE (2026-10-26 ~18:40 UTC): library-only patterns and lemma mining (user-approved items)
- New opt-in code: `MONSTER_LIBONLY=1` (`PatternProp::lib_only`, set on the main solver in `cmd_full` and on cube
  solvers in `glue::hybrid_solver` after the library is imported; library-proving solvers are unaffected),
  `MONSTER_ADMIT` also prints pattern sources (`source_split`); `MONSTER_MINE=k,budget,tries,every` (`full::mine_lemmas`,
  `Solver::recent_learnts`; mined lemmas are proved in the main solver like inline library lemmas, proofs verified).
- **Library-only is ~6x faster on the R(4,5) d=8 hybrid sample** (575 s vs 3,400 s on 15 common pairs, 1.39x conflicts),
  but loses on small full formulas (learned patterns earn their cost there). Running `symsat-d10-hybrid-libonly` (16 d=10
  units, compare with unit mode's stored base/tasks.jsonl in results/ab/r45d10_unit_vs_hybrid) -- this may reopen the
  d=10 engine choice. Also running `symsat-r36k18-libonly{,-vertex}` (R(3,6)/K18 as one formula, 1 h each).
- Mining: 16x on library-free R(3,5)/K14 (k=8), 50x worse on library-free R(4,4)/K18. Next: offline mining for K25,
  cached and reused by every cube.

## 5a''''''''''''. UPDATE (2026-10-26 ~17:00 UTC): diagnosis of the original idea at scale
- 17:49: d=10 unit mode final sample 1,316 s/unit (~67 days for the stage); certified d=8 at 180/358 (all UNSAT);
  d10-allgrayA units still running (break-even ~22,400 s each); K=8 flag still in set-up (241 CPU-min, 3.2 GB).
- New opt-in code: `MONSTER_ADMIT=1` prints pattern-admission reasons and a vertex-count histogram of learned clauses
  (`PatStats::{rej_*, vhist}`); `MONSTER_BRANCH=vertex` (vertex-major decisions, `Solver::pick_branch`).
- Finding (RESULTS.md "Why symmetric learning stalls at scale"): learned clauses are global on R(3,6)/K18 and K25 (most
  span all vertices), so 99.9% are rejected as patterns; pattern search is 94-97% of run time. Vertex-major branching:
  2.8x faster per conflict on R(3,6)/K18, but learning is not more local.
- Next: grow the deliberately local lemma library (mined obstructions proved by assumption solves) and make the
  search for their images cheaper; the at-scale test (R(3,6)/K18 as one formula, VSIDS and vertex-major) can run meanwhile.

## 5a'''''''''''. UPDATE (2026-10-26 ~16:00 UTC): new angles tried (RESULTS.md, last section)
- 16:36: tails: d=10 961 s/unit (~49 days), d=12 485 s/unit (~78 days); node throttle neutral on complete solves.
- Code: `--book-axioms` for pair mode (`encode::pair_book_axioms`, guarded sequential counters `at_most_if`,
  tests `encode::book_tests`); measured negative on time (x21) for -21% conflicts. Flags: min-degree cases [12,13]
  refuted, [11,13] and "no 8, no 10" not.
- Running: `symsat-d10-allgrayA` (d=10, small side free, 4 units of 4,157; decides whether d=10 can be 17x fewer units),
  plus the jobs listed below.

## 5a''''''''''. HAND-OFF UPDATE (2026-10-26 ~15:30 UTC)
- **Decided:** unit mode is the d=10 engine (hybrid 11x/24x slower on gray units; kill criterion met, hybrid side stopped).
- **d=12 cover built:** `results/covers_r45/c44_12_g8.txt`, 18,517 gens (v10: 20,346); d=12 = 222,204 units.
- **New code (opt-in, default behaviour unchanged):** `MONSTER_NODE_THROTTLE=X` (pattern throttle by nodes per image,
  src/pattern.rs) and `MONSTER_PATVIV=1` (vertex vivification of stored patterns at root restarts,
  `Solver::vivify_patterns`, `rup_at_root`; patterns can be retired). PATVIV shrank 0 of 18 K25 patterns.
- **Running now (read first):** `symsat-ab-throttle` (d=8 sample, throttle 30k vs off, 3+3 workers ->
  results/ab/r45d8_throttle30k, row in bench/ab.jsonl); `symsat-d12-sample` (16 d=12 units, unit mode, 4 workers ->
  results/ab/r45d12_unit_sample/tasks.jsonl; extrapolate x 222,204 / 16); `symsat-d8-certified` (all 358 d=8 pairs,
  every task checked -> results/overnight/d8_certified; slow at 4 workers, restart with more workers once the box is
  free, `--resume` skips finished tasks); `symsat-ab-r45d10` (only unit mode left, finishing its last 2 hard units; the
  ab row will not be written because the hybrid side was stopped: read base/tasks.jsonl); `symsat-flag-r45-k8`.
- Ideas from the 15:00 review pastes and their status: IDEAS.md, last table.

## 5a'''''''''. HAND-OFF (2026-10-26 ~14:45 UTC): what is running, where results land, what to do next
- **Running (capped units; read them first):**
  - `symsat-ab-r45d10`: `monster ab`, R(4,5) d=10 A6B6 units, unit mode (base) vs hybrid pattern CDCL (cand), 16 of
    70,669 units, seed 1, 4+4 workers. Results `results/ab/r45d10_unit_vs_hybrid/{base,cand}/tasks.jsonl`, one row in
    `bench/ab.jsonl` when both sides finish (the hybrid side is ~10x slower, so it may take hours). At 14:45: unit mode
    9 units, 417 s and 2.29M conflicts per unit (box loaded by the other jobs) -> d=10 ~ 70,669 x 417 s = ~8,200 CPU-h,
    ~3 weeks on 16 cores; hybrid 1 unit (611.7 s vs 54.6 s in unit mode on the same unit, half the conflicts).
  - `symsat-cover-d12`: `monster cover --s 4 --t 4 --n 12 --gray 8` -> `results/covers_r45/c44_12_g8.txt` (v10's
    builder found 20,346 gens in 688 s; ours is slower). Then measure d=12 with an ab sample: `glue --s 4 --t 5 --n 25
    --d 12 --covers results/covers_r45 --gray-a 0 --gray-b 8 --mode unit --sample 16`.
  - `symsat-flag-r45-k8`: `monster flag --s 4 --t 5 --n 25 --k 8` (old binary, no degree blocks), in set-up since
    13:45 (52 CPU-min at 14:45). Output `results/flag/R45_N25_K8/` (csdp.log, problem.sol) and its journal.
- **Where R(4,5) <= 25 stands:** not proved. Flag SDP: <= 28 at K=7, nothing at K=7 settles N=25 (degrees, parity,
  d=10 case split all tried). Gluing: d=8 ~1.1 h wall; d=10 ~3 weeks in unit mode; d=12 cover being built.
- **Next, in order:** (1) read the three jobs' results; (2) cut d=10 cost per unit inside monster's unit mode (port v11-style cubing / inprocessing, never run CaDiCaL or v11:
  v11 needed 1.72x fewer conflicts) and judge every change with `monster ab` on the same 16-unit sample; (3) cover
  optimisation by predicted cost, not unit count (IDEAS candidate 1); (4) d=12 sample once its cover exists;
  (5) if K=8 certifies or comes close, add the degree/parity blocks at K=8.

## 5a''''''''. Earlier (2026-10-26 ~14:30 UTC): user picked items 1, 2, 5 (d=10 engine decision, d=12 cover, flag research)
- Flag research (5): `--parity` (exact degree distribution via Lagrange polynomials in r, x_j >= 0, handshake lemma for
  odd N) and `--exclude-degree j` (one half of a case split; output says so) added; coefficients are now exact integers
  (`coeff_int`) with per-block power-of-two scaling. Nothing settles R(4,5) at K=7 (RESULTS.md table); the surviving
  fractional solution looks 10-regular. Assumption-only probes: all-degree-8 and all-degree-12 refuted, all-degree-10 not.
- d=10 engine (1): `monster ab` got `--base-args` / `--cand-args`. Running `symsat-ab-r45d10`: unit mode vs hybrid
  on the A6B6 cover (results/covers_r45 links the v10 covers), 16 of 70,669 units, seed 1, 4+4 workers. First common unit
  (3,392 pairs): unit 54.6 s / 683,802 conflicts, hybrid 611.7 s / 333,913 conflicts.
- d=12 cover (2): `symsat-cover-d12` builds results/covers_r45/c44_12_g8.txt (the v10 log says 20,346 gens, i.e.
  244,152 units with the 12 r35 graphs); started 14:07, 8 workers.
- K=8 flag job `symsat-flag-r45-k8` still in set-up (45 min CPU at 14:30).

## 5a'''''''. Latest (2026-10-26 ~14:00 UTC): idea 3 works: exact flag-algebra certificates (`monster flag`)
- 14:05: `--degree auto|LO,HI` adds localising blocks (red degree in [LO,HI], integrality); the coefficient engine is now
  general (exact weight depends only on the union size of a sampled structure). Negative for R(4,5): K=7 gives
  λ = -1.15e-7 at N=25 with degrees vs -1.39e-7 without, and the N=24 control scores the same (-1.74e-7). K <= 7 cannot
  separate 24 from 25 vertices. K=8 (unit symsat-flag-r45-k8, old binary, no degrees) still in set-up at 14:02.
- Gluing-route cost (RESULTS.md): d=8 ~1.1 h wall; d=10 = 70,669 A6B6 units, ~4.4 days at v11's CaDiCaL speed or
  ~18 days at monster's unit-mode speed; d=12 cover unfinished.
- `src/flag.rs`, `monster flag --s S --t T --n N --k K`: finite-N flag SDP, CSDP (`apt install coinor-csdp`, untrusted)
  finds the certificate, Rust checks it exactly (integer Cholesky factors, checked i128). Outputs in
  `results/flag/R{s}{t}_N{n}_K{k}/`. Tests: `flag::tests` (class counts, exact identity on random colourings).
- Proved with exactly checked certificates: R(3,3) <= 6 (K=3), R(3,4) <= 9 (K=5), **R(3,5) <= 14 (K=6, 0.07 s)**,
  **R(4,4) <= 18 (K=6, 0.28 s)**, R(4,5) <= 28 (K=7). Not certified: R(4,5) <= 25..27 at K <= 7 (optimum at the
  boundary, ~-1e-7). Every positive control (N = R-1) gives no certificate. Table in RESULTS.md.
- Running: `symsat-flag-r45-k8` (K=8 at N=25; 12,346 classes before filtering, big SDP, may take hours or run out
  of the 40G cap). Next if it fails: degree-localising constraints (red degree in [7,13] from R(3,5)=14 and
  R(4,4)=18, as in Angeltveit-McKay's R(5,5) <= 46 LP), i.e. E_v[(r_v-7)(13-r_v) v vᵀ] PSD for the vertex type.
- Trust: the certificate check is exact, but it rests on src/flag.rs computing the coefficients right (tested
  against direct expectations) and on the class enumeration being complete. A Lean statement of the identity would
  close that gap later.

## 5a''''''. Earlier (2026-10-26 ~13:30 UTC): incremental matching probed, two negatives; idea 3 next
- User asked for idea 3 (symmetric SOS / flag algebras, never started) and incremental matching (03:10 plan #1).
- Incremental matching across assignments, measured (RESULTS.md, last section): exact repeats of fruitless scans are
  0.8% (K25) and ~1.2% (R(4,5) d=8 hybrid) of scans, because `sync` already skips the unchanged trail prefix; global
  candidate sets (arc consistency over the whole colouring, slack-aware, soundness asserted) prune 0.01% of nodes. Both
  removed. Kept: per-literal scan counter (`PatStats::scans`, `scans` in glue task records).
- Engine speed now has to come from cheaper deep search or fewer searches: the top K25 pattern (k=9, e=22) spends 77M
  of 206M nodes for 610 images; a per-pattern yield bandit (IDEAS RL #1) judged by `monster ab` on the d=8 sample.

## 5a'''''. Earlier (2026-10-26 ~12:15 UTC): measuring gains on the full run (`monster ab`), library stamps
- **How to judge a change from now on:** `monster ab --base REV|BIN -- glue <the full run's args> --sample K`.
  Both binaries solve the same seeded task sample at the same time (`--sched static`, `--check-every 0`, `--chunk 1`
  and `--workers threads/2` are added unless given). It checks that every task's verdict agrees (a disagreement fails
  the command) and prints, for secs / conflicts / search nodes / embed calls, the ratio of totals with a bootstrap 95%
  interval, the per-task geometric mean, and the full run's CPU time extrapolated from the sample via `plan_pairs`.
  One row per comparison goes to `bench/ab.jsonl`. `--base HEAD` (the default) builds the last commit once into
  ~/.cache/symsat/base/<sha>/; `--base-env MONSTER_LEGACY_EMBED=1` compares against the old embedding search.
  Code: `src/ab.rs`.
- **Why runs took 10+ minutes:** every hybrid run re-verified the cached lemma library single-threaded
  (R(3,7)/K23: 67 MB, ~650 s, before any solving). Now `<cache>.verified` holds "symcheck-1 sha256" after a successful
  check and uncertified runs (`--check-every 0`) skip the re-check when the stamp matches the file's bytes.
  Certified runs still re-check up front (and their task proofs contain the library proof anyway, via `import`).
  Bump `VERIFY_TAG` in src/full.rs when the symmetric checker changes.
- glue: `--sched static` (worker w runs tasks w, w+W, ...; hybrid workers keep their solver across tasks, so the
  first-come schedule made per-task counts depend on thread timing); task records now carry `nodes` and `embed`
  (pattern search); summary.json carries `plan_tasks` / `plan_pairs` (the unsampled plan).
- **Measured on the real hybrid workload (R(3,7)/K23, same 12 tasks / 359 pairs):** old embedding search 1,155 s,
  domain search 229 s (**5.0x**), conflicts 108,958 vs 110,071. The domain-search run completed all 2,583 pairs
  (UNSAT, uncertified) in 3m54s of solving on 7 workers; 666,449 conflicts, 1,615 CPU-s.
- **Session ended at ~12:20 UTC (session limit).** Still running as capped units (check with
  `systemctl --user list-units "symsat-*"`):
  - `symsat-ab-r45d8`: `monster ab` on the standing R(4,5) d=8 sample (16 of 358 pairs, seed 1), base = this binary
    with MONSTER_LEGACY_EMBED=1, cand = domain search. Output `results/ab/r45d8_domain_vs_legacy/` and one row in
    `bench/ab.jsonl` when done (~12:30-12:45). Early, same pair (d=8, fixed 0, lo 85): old 206 s / 29,776 conflicts,
    new 64.9 s / 22,782 conflicts (3.2x). New-search pairs take 65-196 s each.
  - DONE 12:51: verdicts agree on all 16 pairs; time ratio 0.321 (95% CI 0.279-0.390), conflicts 0.709, nodes 0.435;
    full d=8 run extrapolated 55.6 -> 17.9 CPU-h (3.5 h -> 1.1 h at 16 workers). Reference row for later changes.
  - `symsat-stamp-r37` DONE 12:25: R(3,7)/K23 library (10 lemmas, 284,175 proof lines) VERIFIED in 895 s; stamp
    `results/library_R37_K23_books.bin.verified` written, so R(3,7) samples now start in seconds. Next run:
    `monster ab --base-env MONSTER_LEGACY_EMBED=1 --base target/release/monster -- glue --s 3 --t 7 --n 23 --route all
    --mode hybrid --sample 64 --seed 1` (expected ~1-2 min).
  - Read both results first in the next session and record them in RESULTS.md.
- Fixed this session: `--proof` on the new default `--lib lift` died ("checked through SLRAT"); it now writes a
  temporary SLRAT file and checks it with the reference checker. All five library modes verify with `--proof`;
  `tests/regression.rs::documented_quick_check` guards the documented command. RESULT lines now report the SLRAT
  verdict too (was "unchecked").
- Next for measurement: a fixed R(4,5) d=8 sample as the standing benchmark for the target run (its pairs cost
  ~100-600 s each, so use `--sample 16`); make `Library::get` (hybrid) use the separate/lift path (the R(3,7)/K23
  library build took ~13 min inline).

## 5a''''. Earlier (2026-10-26 ~11:40 UTC): domain-based embedding search (incremental domains within one search; the
  cross-assignment incremental matching of the 03:10 plan, Rete / IVM / WCOJ, is still open, see IDEAS.md)
- `src/pattern.rs::DomSearch` replaces `rec` + `forward_ok` as the default embedding search. Per unmapped pattern
  vertex it keeps two u64 bitsets, strict candidates and candidates with exactly one unassigned edge (the slack), updated
  incrementally when a neighbour is placed (one AND/OR each). Initial domains come from degree-threshold masks
  `rge[d]`/`bge[d]` rebuilt once per sync. Each node: empty-domain check, at most one vertex on the slack, a Hall bound
  (|union of constrained domains| >= #constrained), then smallest-domain-first branching. Leaves/book pages still go
  to `place_leaves` (matching). Pure pruning: the search is complete, so whether an image exists is unchanged.
- `MONSTER_LEGACY_EMBED=1` runs the old search; `MONSTER_CHECK_EMBED=1` runs both on every call, asserts they agree and
  that every image is valid (distinct vertices, no wrong-coloured edge, <= 1 unassigned). Passed on 2.9M K25 calls
  and on R(3,4)/K9, R(3,5)/K14, R(4,4)/K17-18, R(3,6)/K17 at relabel 0/7, inline and lift-inline; all UNSAT proofs
  pass the Lean checker.
- K25 profile (6000 conflicts, cached library): propagation 34.4 s → 13.5 s, total 39.1 s → 18.2 s, nodes/call 99 → 70.
  Tried and dropped: an unused-neighbour degree filter (-0.2% nodes), most-mapped-neighbours-first ordering (worse)
  and size/c ratio (same).
- Running at 11:32 (capped units): `symsat-bench-lib` (bench, 4 instances x 4 lib modes, 32 samples ->
  `results/bench/libmodes_2026-10-26.jsonl`), `symsat-hyb37-domain` / `symsat-hyb37-legacy` (hybrid R(3,7)/K23, 4 workers
  each, 1800 s timeout, -> `results/overnight/embed_cmp/`).

## 5a'''. Earlier (2026-10-26 ~10:56 UTC, recovered 11:15): order-independent library, `monster bench`, `--lib lift`
- The session was cut off mid-turn (~10:56; box down 10:50–11:08, rebooted). The code below was never committed to
  main by the Stop hook (the turn never ended) but was in `backup/auto`; on recovery it builds and `cargo test` passes
  (17 unit + 5 regression). Numbers below are recovered from the transcript's tool output.
- New in `src/full.rs`, `src/main.rs`, `src/sat/solver.rs`:
  - `--relabel SEED` (random vertex permutation; odd seeds also swap colours when s = t), `--phase blue|red|random`.
  - `--lib inline|separate|lift|lift-inline`: library proved in the main solver, in a separate solver imported in
    canonical order, or with the stars lifted from sub-instances (R(3,5)/K14, R(4,4)/K18 for K25) via the lift rule.
  - For s = t, one lemma per colour-swap orbit (blue-heavy rep; `MONSTER_ORBIT_REP=red`, `MONSTER_NO_ORBIT=1`).
  - `SlratWriter` renumbers lines from several solver logs and emits sub-instances / lift lines, so spliced proofs
    stay Lean-checkable.
  - `monster bench --samples K`: relabelled runs, median/p90/max of conflicts, split into library and main.
- Verified: `--lib lift-inline` proofs for R(3,3)/K6, R(3,4)/K9, R(3,5)/K14, R(4,4)/K18 at relabel 0/7/8 all pass
  the reference checker and the Lean checker. R(4,4)/K18 lift-inline: 537 / 52 / 135 conflicts (seeds 0/7/8).
- Bench (32 samples), R(4,4)/K17 (SAT): inline med 530, p90 1478, max 3427; separate med 735, max 979; lift med 552,
  p90 617, max 777 (lib med 40). So separate/lift remove the heavy tail; inline has the best median on small cases
  (R(3,4)/K9 inline med 31 vs separate/lift 74, max 221).
- K25 library: inline 23,069 conflicts / 1.46 s; lift 10,292 / 0.79 s (stars lifted: red 762, blue 128 conflicts).
- Not finished: the 32-sample `bench --lib lift-inline` on R(4,4)/K17 (killed by the shutdown); RESULTS.md and
  README not yet updated for the new flags; the regression gate still uses the inline path.

## 5a''. Earlier (2026-10-26 ~09:50 UTC): backups, lemma history, regression gate
- **Backups and context:** see §4. Conversations are exported to `context/chats/` and pushed with every snapshot.
- **Lemma history measured** (R(4,4)/K18 and R(3,5)/K14 at every lemma/pattern/solver commit, both paths; table in
  RESULTS.md). Nothing was lost: the books path improved at each step (R(4,4): 1,123 → 921 → 406 → 129 conflicts).
  The only regression is stars-only at 1a60950 (599 → 2,607). The 03:17 and 05:17 auto-backups changed no counts.
- **Cause of the stars-only regression, verified:** lemma proof order. Proving the red star before the blue star
  restores 599 exactly; the same reorder makes the books path 713 instead of 129. So R(4,4)/K18 swings 129–2,607
  conflicts on lemma order alone: the main search is chaotic in the library's proof order (the proofs run in the
  main solver and leave their learned state behind). Relevant to "consistent solve times"; not fixed, only avoided.
- **`--books` is now the default** (`--no-books` = stars only), so the documented commands give 129 conflicts.
- **Stale lemma caches fixed:** `Library::get` used to accept any cached `results/library_*.bin` with matching (s,t,n),
  so hybrid runs and the K25 profile kept loading the pre-1a60950 library (K25: 6 lemmas instead of 11). The cache now
  carries a format tag (`LIBRARY_MAGIC` "MON2", bump it whenever the lemma set changes) and the books flag; stale files
  are rebuilt. The K25 cache is rebuilt (11 lemmas); the other cached libraries rebuild on first use.
- **Regression gate:** `tests/regression.rs` (in `cargo test`): R(3,3)/K6, R(3,4)/K9, R(3,5)/K14, R(4,4)/K18 must stay
  UNSAT with verified proofs (reference checker, plus the Lean checker when built) under conflict ceilings of about
  1.5× today's counts, and R(4,4)/K17 must give a verified witness. Shown to fail when a ceiling is exceeded.

## 5a'. Earlier (2026-10-26 ~09:15 UTC): lift rule landed
- Local symmetry, done the sound way. A sub-instance F(s',t',m) has its own database, opened with `o s' t' m` and
  stepped with `s k <line>`; colour swap is allowed inside it when s' = t'. Lift line `id l k src v r|b e0..e{m-1} 0`
  adds e(C) plus m apex-context literals to the main database. It is proved in Lean (`verified/MonsterVerified/Lift.lean`,
  `stepFn_ok`) and mirrored in the Rust reference checker. Code is in `src/lift.rs`: `monster lift-demo` writes test
  proofs with monster's own CDCL, `monster lift-test --lean verified/.lake/build/bin/checker` runs 3 accepted proofs
  and 20 rejected mutants against both checkers, and `monster slrat2lean` builds kernel-only theorems.
  Details are in RESULTS.md and verified/SOUNDNESS.md.
- Never swap colours on a main-database clause under a neighbourhood context. Main clauses may depend on constraints
  outside the neighbourhood. Only clauses derived inside the sub-instance's own database may be swapped and lifted.
- Next, in order:
  (a) Solver support: prove blue-apex R(4,4) and red-apex R(3,5) sub-lemmas for R(4,5)/K25, emit lift lines, and
      measure embedding nodes, not just conflicts.
  (b) Make the context cheap. Store a lift as a descriptor (lemma, apex, polarity) and test the context with one
      bitset subset check, e(0..m-1) ⊆ N_colour(v), instead of an (m+1)-vertex pattern.
  (c) Shrink the context with proof supports (unverified idea). If a sub-proof only uses clauses over U ⊆ K_m, context
      on U would suffice. This needs a checked "support" notion; the current rule deliberately requires all m.
  (d) Lemma families as descriptors with popcount propagators (degree bounds), with reasons generated on demand and
      RUP-checked. This is the same step as native cardinality reasoning.
  (e) Benchmark against SMS and SEL, then write up the lift rule as the proof-system contribution.
- Do not expect a jump on R(3,6): its sub-instances are R(3,5) and the trivial R(2,6), so no swap applies there.
- Stars-only regression: superseded by 5a'' (cause verified, `--books` now the default).

## 5b'. What ended the previous session (2026-10-26 04:29 UTC), and rules from it
- 04:20 UTC: the session converted the 689-line `verified/proofs/R44_K18.slrat` to a Lean term and started the
  kernel-only check (`lake env lean`) with `setsid nohup`. That process stayed inside the tmux scope's cgroup and grew to
  64 GB RSS (the box has 62 GiB and no swap).
- 04:29:09: the kernel OOM killer killed that one `lean` process. 04:29:10: systemd (user manager, DefaultOOMPolicy=stop)
  logged `tmux-spawn-6d1494c5-….scope: Failed with result 'oom-kill'` and stopped the whole scope. That killed the tmux
  server, the Claude session, and the R(3,6)/K18 `--cube-lemmas` test it was running (exit 137, no result).
  `results/kernel_R44.log` is empty for that reason. Kernel-only R(4,4) is NOT done. Evidence: `journalctl --since
  "2026-10-26 04:29" --until "04:31"`.
- one_d8/one_d12 were not involved: they had been stopped at 03:14.
- The untested `--cube-lemmas` code (src/full.rs `add_cube_lemmas`, written at 04:22) was auto-committed at 05:17,
  because cargo build and test passed. It has never been run to completion. Test it before relying on it.
- Rules:
  1. `setsid nohup` does NOT leave the cgroup. Anything started from the session dies with the session's scope. Run
     long or memory-heavy jobs (Lean kernel checks, big solves) with `scripts/capped.sh NAME 40G CMD...` (its own
     systemd user unit `symsat-NAME`, MemoryMax plus MemorySwapMax=0; logs `journalctl --user -u symsat-NAME`). An OOM
     then stops only that unit. `ulimit -v` breaks Lean (thread creation). Linger is off until
     `scripts/install_backups.sh` runs, so until then the user manager (tmux, timers, capped jobs) lives only while
     some login session exists; session 1 has been open since boot.
  2. The Claude Bash sandbox has a private /tmp, so `tmux ls` inside it always says "no server". Check tmux and
     processes outside the sandbox before reporting what is running.
  3. Tooling is Rust (in the monster binary), not Python. The solver is Rust; tests and generators go in `cargo test`
     or `monster <subcommand>`.
  4. On a fresh session, read the previous conversation in `context/chats/` (exported from
     ~/.claude/projects/*/*.jsonl by scripts/export_context.sh), especially its last messages and commands.

## 5a. Earlier (2026-10-26 ~04:15 UTC)
- Lean-verified checker done (verified/), including the colour-swap rule (S_N × Z_2 when s = t).
- Antisymmetry: colour-swap patterns for R(s,s) (R(4,4)/K18 890 → 599 conflicts).
- General rooted lemmas (a red roots, b blue roots, R(s-a,t-b) leaves, cross edges free): R(4,4)/K18 129 conflicts,
  0.022 s, Lean-verified. The R(4,5) K25 library now builds in < 2 s.
- Running: R(3,6)/K18 as a single formula with general rooted lemmas (never solved before).
- Ideas queued (see IDEAS.md / chat): contextual import of sub-instance lemmas (F(s-1,t) / F(s,t-1) lemmas lifted
  into F(s,t) with a vertex-colour context; colour swap usable inside the symmetric sub-problem), injective-map image
  rule (lemmas proved on smaller K_m), incremental matching (#1).

## 5. Current numbers (details in RESULTS.md)
- Full formula, proofs verified: R(3,5)/K14 0.24 s, R(4,4)/K18 0.59 s. R(3,6)/K18 is NOT solved as one formula
  (needs cubes; hybrid solves it, certified).
- K25 profile (6000 conflicts, library loaded): 315 s → 43 s tonight (embedding-search work).
- Hybrid R(4,5) d=8: ~44k conflicts/pair (pair mode ~122k) but ~600 s/pair (pair mode ~4 s). Pattern search cost per
  conflict is the bottleneck; the remaining cost sits in ~15 learned patterns of 9–11 vertices.

## 5b. Verified checker (Lean 4, `verified/`)
- `lake build` in `verified/` re-proves everything. Main theorem `MonsterVerified.check_sound`
  (Checker.lean). `#print axioms` gives propext, Classical.choice, Quot.sound only (`lake env lean MonsterVerified/Axioms.lean`).
- Executable `verified/.lake/build/bin/checker FILE.slrat`; theorems via native_decide (trust the compiler) or
  kernel-only via `monster slrat2lean proof.slrat Name > Name.lean` (small proofs; run under a memory cap).
- Any change to the SLRAT format must be mirrored in `verified/` and re-proved.

## 6. Next steps, highest expected impact first
**Current focus (user, 2026-10-26): #1 incremental pattern matching, #3 verified checker (done at prototype scale),
antisymmetry (colour swap for R(s,s), cross-instance transfer via complement, dynamic antisymmetry), and
preprocessing that keeps solve times consistent, all at full verification standard.**
0. (paused) **One-sided cubes**, `glue --mode hybrid --one-sided`).** Only the smaller catalogue side of vertex 0
   is fixed by assumptions; the other side is free, and the lemma library proves its constraints inside F. R(4,5)
   cube counts: d=8 → 2, d=10 → 313, d=12 → 12 (instead of 358 / 40.9M / 17.4M pairs). This also removes the big r44
   catalogues from the trusted base (only r35 levels, ≤313 graphs, remain). Ladder check running:
   R(3,5) N=13/14, R(4,4) N=17 passed with every cube certified. R(3,6) N=17/18 did NOT finish in 900 s (the free
   side is as hard as R(3,6)/K18). R(4,5) d=8/d=12 one-sided runs are going. If they stall, try partial cubes: the small
   side fixed plus a gray-edge generalisation of the large side (v10 covers), cubing on base edges only.
1. **Pattern quality.** Offer vivified (shortened) learnt clauses to the pattern store (`Solver::vivify` already logs
   them). Smaller patterns are cheaper to search and more general. Benchmark: hybrid R(3,7) N=23
   (`glue --s 3 --t 7 --n 23 --route all --mode hybrid --books --check-every 0`).
2. **Fewer embed calls.** Index patterns by anchor degree requirements; add stronger exact necessary conditions.
3. **Does pattern memory compound?** Analyse `results/overnight/hyb_d8/tasks.jsonl` conflicts per pair against task order
   per worker. If yes, hybrid can win on d=8/d=10. If not, export library or patterns into pair mode instead.
4. Symmetric SOS / flag algebras (idea 3): not started.
4a. Reinforcement learning (bandits) for pattern admission, per-cube parameters, branching: see IDEAS.md.
4b. **Defined goal:** end-to-end verified R(4,5)=25 from the plain formula (cube lemmas proved in F, then pattern CDCL
    derives ⊥ from cube lemmas + images + library, removing the trusted catalogue-completeness step). See IDEAS.md,
    "External review notes". Do NOT use SR steps with σ as witness for images; that is unsound with learned lemmas.
5. Native cardinality (PB) reasoning with VeriPB logging for degree/book constraints (arXiv 2203.12275).

## 7. Instructions for Claude (operational lessons)
- **Back up often**: commit and push after every meaningful step with a real message. The hooks (§4) are the safety
  net: snapshots to `backup/auto`, and gated "auto:" commits to main at the end of each turn. With every code change,
  update this file (the Stop hook insists), and RESULTS.md / README.md / CLAUDE.md when numbers, usage or rules change.
- **Never `pkill -f`/`pgrep -f <pattern>` in a command whose own text contains the pattern**: it matches and kills
  your own shell (happened five times). Look up PIDs in one tool call (`pgrep -a monster`), kill by number in the next.
- Long jobs: `scripts/capped.sh NAME MEMORY CMD...` (never `setsid nohup`, see 5b'); write to `results/overnight/`.
- `--sample`/`--d` runs are estimates or stage results, never claims about R(s,t).
- Judge speed changes by deterministic counters (search nodes, embed calls, conflicts) when the box is busy.
- Before any claim: run the checker (symmetric checker at scale, cake_lpr when small).
- The user prefers: highest-impact work, no pointless comparisons, verification first, honest verdicts, regular backups.
