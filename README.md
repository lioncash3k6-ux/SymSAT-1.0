# SymSAT: symmetric-learning SAT solving for Ramsey numbers, with a formally verified checker

SymSAT solves Ramsey problems on the **full, unreduced formula**. "R(s,t) ≤ N" means no 2-colouring of K_N avoids a
red K_s and a blue K_t. It exploits symmetry *as an inference rule* rather than by breaking it:

- **Pattern CDCL.** Every learned clause is stored once as a canonical forbidden 2-coloured pattern. Its images
  under vertex permutations (and, for R(s,s), under colour swap) are found by embedding search and propagated lazily.
- **Recursive lemma library.** Rooted lemmas (stars, books, mixed books) whose sizes come from smaller Ramsey numbers
  are **proved inside F** by the solver, verified, cached and reused as patterns.
- **Verification.** Proofs are written in **SLRAT**: LRAT plus image lines `σ(C)`, linear size, no expansion. They
  are checked by a **Lean 4 checker whose soundness is proved**: `MonsterVerified.check_sound` says that if the
  checker accepts, then every 2-colouring of K_n has a red K_s or a blue K_t. It depends only on Lean's standard
  axioms (`propext`, `Classical.choice`, `Quot.sound`).

The solver binary is still called `monster` (its original name); `verified/` holds the Lean project.

**SymSAT 1.0** (2026-10-28): public release, MIT license (`LICENSE`). Public repo: https://github.com/lioncash3k6-ux/SymSAT-1.0
(code, docs, results and data; the working repo's conversation exports are not included). One command to a running Lean
shard on a fresh Debian/Ubuntu box (x86-64 or aarch64; Android via Termux + proot-distro Ubuntu):
```bash
curl -fsSL https://raw.githubusercontent.com/lioncash3k6-ux/SymSAT-1.0/main/scripts/bootstrap.sh | bash -s -- --d 10 --shard 1/4
```
(or `monster bootstrap ...` from a bundle, which embeds the same script). Merge shards: `monster merge-shards --out DIR SHARD...`.

## Results so far (details in RESULTS.md)
| statement | SymSAT solve | proof (SLRAT lines of the stored theorem; today's default: R(3,5) 426, R(4,4) 507) | Lean check |
|---|---|---|---|
| R(3,3) ≤ 6 | instant, 4 conflicts (colour swap) | 19 | kernel-only theorem `R33_le_6_kernel` (no compiler trust) |
| R(3,4) ≤ 9 | 0.003 s, 26 conflicts (plain CDCL: 8,949) | 149 | theorem `R34_le_9` |
| R(3,5) ≤ 14 | 0.005 s, 46 conflicts (default `--lib lift`; worst of 32 relabellings 62) | 2,563 | theorem `R35_le_14` |
| R(4,4) ≤ 18 | 0.008 s, 61 conflicts (worst of 32 relabellings 78; plain CaDiCaL: not solved in 300 s) | 689 | theorem `R44_le_18` |
| R(3,6) ≤ 18 | flag certificate at K=7, 2 s (exact check); as one CDCL formula: open | | |
| R(4,5) N=25 | not yet. Minimum-degree route: d=7,8,9 gluing done (unit mode, 1,625 units, 186,029 pairs, all UNSAT, every unit hint-checked; 12.5 CPU-h; certified end to end: `results/overnight/mindeg_d789_recert9/summary.json` certified_pairs 186029, errors 0); the K=8 flag SDP with `--degree 10,13 --parity` gives NO certificate (λ = 0 to precision, 2026-10-27), and `--degree 11,13` also gives λ = 0: the K=8 flag route is closed; the parity gluing route (d=10 running, then d=12) remains; the catalogue-constrained K=8 SDP (`--nbhd 10,13`) also gives λ = -3.8e-8 (2026-10-27 22:17), so no flag route at K=8. Fallback gluing with cube + drop 90: d=10 70,669 units ~1,642 CPU-h (was ~67 days), d=12 with the new covers `--gray-a 6 --gray-b 8` 37,034 units ~2,600-2,800 CPU-h (was ~6,300 with gray-a 0, ~78 days before that; RESULTS 2026-10-27 ~19:30); parity route total ~12 days on 16 cores. Flag SDP: ≤ 28 at K=7; plain K=8 gives no certificate (λ = -3.3e-8, 15.5 h CSDP) | | |

These are known values. The point is the method: full-formula solving with symmetric learning and verified
certificates. A second, independent method (`monster flag`, flag-algebra / symmetric-SOS certificates checked in
exact integer arithmetic) proves R(3,5) ≤ 14, R(4,4) ≤ 18 and R(3,6) ≤ 18 tightly in seconds and R(4,5) ≤ 28; at K ≤ 7 it
cannot reach R(4,5) ≤ 25 (RESULTS.md). What scales is symmetric *lemmas* (proved once, applied to every image), not
sharing every learned clause: on tight Ramsey formulas CDCL's learned clauses span almost all vertices (RESULTS.md,
"Why symmetric learning stalls at scale"). Next targets: R(4,5) ≤ 25 end-to-end, flags for graph Ramsey numbers.

## Install
Linux x86_64.
```bash
# Rust (solver) and infrastructure (jq for the chat export, gh for pushes, csdp only for `monster flag`)
sudo apt install build-essential jq tmux gh coinor-csdp
curl -sSf https://sh.rustup.rs | sh -s -- -y --profile minimal && source ~/.cargo/env
# Lean 4 (verified checker)
curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | bash -s -- -y --default-toolchain leanprover/lean4:stable
source ~/.elan/env
# Graph catalogues (only for the gluing/hybrid modes): the public repo with v5/catalogs
git clone https://github.com/lioncash3k6-ux/cascade-solver-ramsey-v4-algebraic ~/cascade-solver-ramsey-v4-algebraic
```

## Build and test
```bash
cargo build --release && cargo test --release          # solver: target/release/monster; 26 unit + 6 regression tests
cd verified && lake build && cd ..                      # Lean: proves check_sound and the theorems, builds the checker
```

## Solve and verify (the main workflow)
```bash
# solve the full formula with pattern CDCL + lemma library; write an SLRAT proof (also re-checked by a Rust reference checker)
./target/release/monster full --s 4 --t 4 --n 18 --patterns --lemmas --slrat r44.slrat
# check it with the formally verified Lean checker
verified/.lake/build/bin/checker r44.slrat              # "s VERIFIED UNSAT: R(4,4) <= 18"
# kernel-only theorem (small proofs): convert to a Lean term and let the kernel check it
./target/release/monster slrat2lean r44.slrat R44_kernel > verified/MonsterVerified/R44Kernel.lean
```
General rooted lemmas ("books") are the default; `--no-books` keeps stars only. The library is proved in its own solver
with the stars lifted from the sub-instances (`--lib lift`, default; `inline`, `separate`, `lift-inline` also exist).
`monster bench --s S --t T --n N --samples K [flags]` runs K relabelled copies and reports median, p90 and max
conflicts; judge consistency by those, not by one run.
`monster ab --base REV -- glue <args> --sample K` compares two binaries on the same seeded sample of a run's tasks
(verdicts must agree) and extrapolates both to the full run; rows go to `bench/ab.jsonl`.
`monster flag --s 4 --t 4 --n 18 --k 6` proves R(4,4) <= 18 by a flag-algebra (symmetric SOS) certificate in 0.3 s: CSDP
(`sudo apt install coinor-csdp`, untrusted) finds it and monster checks it in exact integer arithmetic. See RESULTS.md.
Options: `--degree auto` (degree bounds from smaller Ramsey numbers), `--parity` (exact degree distribution and the
handshake lemma, odd N), `--exclude-degree j` (one case of a case split; reported as such, never as a bound),
`--nbhd LO,HI [--handshake] [--nbhd-l L]` (every red neighbourhood is a catalogue (s-1,t)-good graph on LO..HI vertices: rooted
subgraph counts must be a convex combination of the catalogue graphs' counts; trusted input = catalogue completeness; R(4,4) <= 18
certified at K=4 this way, RESULTS 2026-10-27), `--threads N` (set-up threads, default all cores), `--reuse-sol` (reuse a finished `problem.sol` in `--out` when the SDP
input is byte-identical, so only the exact check is redone). Other modes: `monster glue ...`
(catalogue gluing, hybrid/cube modes), `monster cover`, `monster ladder`, `monster lift-demo` / `lift-test` (lift rule);
see docs/ENGINES_AND_HISTORY.md.
`monster unit-lean ... OUT.slrat --lean verified/.lake/build/bin/checker` exports one gluing unit's refutation as a proof over
the full K_N formula and checks it with the Lean checker's `--lemma` mode (`checkLemma_sound`): the clause "no good colouring
extends this unit" is then Lean-verified (assumption rule + deletion lines + streaming parse: batch mode `checker --lemmas LIST [--delete]` verifies many unit files in one process, one at a time, with the driver theorem `batch_sound` (3 d=7 units + 1 mutant: 3 VERIFIED LEMMA, 1 NOT VERIFIED, 15-18 s, 67 MB; SOUNDNESS.md); d=7 units in ~3 s / 51 MB, a d=9 unit with 1.3M lemmas in ~100 s / 67 MB, the hardest certified d=10 unit with 23.2M conflicts and a 6.1 GB proof in 43 min / 307 MB; RESULTS 2026-10-27 ~19:30).
**SR proofs:** the reference checker (`full::check_slrat`) has the substitution-redundancy rule (`id r lits 0 witness 0 pairs 0`,
Buss-Thapen SR: every clause's image under the witness substitution is satisfied or unit-propagated from F ∧ ¬C) and
propagation lines (`id p lits 0`, hint-less RUP). SR clauses live in a second tier: they only preserve satisfiability,
so images and lifts may not use them and a lemma-mode result must be pure; the empty clause in either tier means "no
good colouring". `monster sr-check --s S --t T --n N PROOF.sr [--slrat OUT]` checks a proof in Heule's DSR line
format: his 39-line proof of R(4,4) <= 18 (tests/data/R_18_4_4.sr, MIT) verifies in 0.25 s. **The Lean checker has the SR
rule** (verified/MonsterVerified/SR.lean, invariant "some good colouring satisfies both tiers"; SOUNDNESS.md): `--slrat OUT` writes
the hinted form (α hints + one hint group per clause, 1.9 MB for Heule's proof) and `verified/.lake/build/bin/checker OUT`
prints VERIFIED UNSAT in 0.9-1.7 s / 28 MB; `monster slrat-hints IN OUT` hints `sr-gen` output (R(3,3), R(3,4), R(3,5), R(4,4)
refutations Lean-verified in <= 1.5 s; the K_25 degree bounds: 70 MB hinted, every line Lean-checked in 54 s / 51 MB, "VERIFIED STEPS"
since the result is SR-tier).
`monster sr-gen --s S --t T --n N OUT.slrat [--bounds]` generates SR proofs of the degree argument (src/srgen.rs): refutations
of R(3,3) <= 6, R(3,4) <= 9, R(3,5) <= 14, R(4,4) <= 18 (8 to 62 lines) and, with `--bounds`, the K_25 clauses "red
degree of vertex 0 in [7,13]" (124 lines, 103 KB, checked in 14 s), which replace the trusted degree bounds of the route.

`monster unit-lean-stage --s S --t T --n N --d D --covers DIR --gray-a GA --gray-b GB --out DIR [--workers W] [--batch K] [--keep] [--resume] [--lean BIN]`
runs a whole gluing stage through Lean (src/leanstage.rs): W workers export every unit of the stage as `unit-lean` does, a
collector hands batches of K files to one Lean process (`checker --lemmas LIST --delete`, `batch_sound`), and `DIR/verified.jsonl`
records the clause Lean printed for each unit, `DIR/summary.json` the totals. R(4,5) d=7: 8/8 units in 69 s; d=8: 30/30 in 25 min
with 3 workers, Lean peak 136 MB, 3.2 GB of proofs written and deleted (RESULTS "2026-10-28 ~00:46"). Proof files are gitignored.

`monster assemble-spec --s 4 --t 5 --n 25 --d D --covers DIR --gray-a GA --gray-b GB --out DIR (--from-record FILE | --proofs LIST | --fake) [--spec FILE] [--threads K]`
writes the untrusted hints (cover permutations) and a `stage D` block of SPEC for `checker --assemble SPEC` (src/assemble.rs,
verified/MonsterVerified/Assemble.lean): the Lean assembler decodes the two graph6 catalogues, reads the unit clauses (`--from-record`:
the `verified.rec` that `unit-lean-stage` now has batch mode write; `--proofs`: SLRAT files it verifies itself, no hypothesis;
`--fake`: exact unit clauses unverified, timing only) and checks in parallel that every catalogue pair is refuted, printing
`s STAGE D REFUTED` with the theorem (`stageRefuted_of_verified` / `stageRefuted_of_record`), and `s R(4,5) <= 25 ASSEMBLED`
(theorem `r45_le_25_of_stages`, hypothesis `CatalogueComplete`) once stages 8, 10 and 12 are all refuted in one spec. d=7 end to
end: `cargo test assemble_d7` (2 min); coverage check alone: d=10 229 s / 361 MB, d=12 138 s / 597 MB, 14 threads (RESULTS "2026-10-28 ~11:00").

Speed of the Lean route (2026-10-28 ~11:30, RESULTS): `unit-lean` / `unit-lean-stage` solve with cube-and-conquer like
unit mode (`--cube-budget C`, default 5,000; conflict counts now equal the certified run's), the Lean checker reads proof
lines with a byte-level parser (`parseLineFast`; `checker --parse FILE` times parsing alone), and the stage driver runs up
to `--lean-jobs J` Lean batch processes at once (default = workers; record files per batch in `DIR/rec/`). Lean checks
~0.18 s per MB of proof; a hard d=10 unit costs ~124 s solve + ~89 s Lean.

Other machines for the Lean stages: (a) any x86-64 Linux box without toolchains: `scripts/bundle.sh OUT.tar.gz` (binary,
checker, catalogues, covers, 57 MB), then `./run_lean_shard.sh D I N [WORKERS] [LEAN_JOBS]` on the box (shard I of N of
the degree-D Lean stage; `unit-lean-stage --shard I/N`); (b) any Debian/Ubuntu box, x86-64 or aarch64, or Android via
Termux + proot-distro Ubuntu: `scripts/bootstrap.sh [--d D] [--shard I/N]` installs Rust and Lean, clones both repos,
builds, and starts the shard (RESULTS "2026-10-28 ~12:40"). Bring back each shard's `verified.jsonl` (concatenate into the
main stage's file, rerun with `--resume`) and its `rec/*.rec` files (one directory, `assemble-spec --from-record DIR`).

Restart from a new machine: CONTINUE.md §0a (everything needed is in git, including the running job's resume log).

## Experimental switches (opt-in; defaults unchanged; measured verdicts in RESULTS.md)
| switch | effect | verdict so far |
|---|---|---|
| `MONSTER_LIBONLY=1` | only proved library lemmas are patterns in the main / cube solvers | **5.9x faster on the R(4,5) d=8 hybrid sample**; 5.8x slower than unit mode on d=10 units; worse on small full formulas |
| `MONSTER_MINE=k,budget,tries,every` | lemma mining: refute sub-clauses of learned clauses on their k densest vertices | 16x on library-free R(3,5)/K14, 50x worse on R(4,4)/K18 |
| `MONSTER_BRANCH=vertex` | vertex-major decisions instead of VSIDS | 36x on R(3,6)/K17, far worse on R(4,4)/K17: portfolio candidate |
| `MONSTER_ADMIT=1` | pattern admission reasons, learned-clause vertex histogram, pattern sources | diagnostics |
| `MONSTER_NODE_THROTTLE=X` | try costly patterns (> X nodes per image) on 1 anchor in 4 | neutral on complete solves |
| `MONSTER_PATVIV=1` | vertex vivification of stored patterns (unit propagation) | 0 of 18 K25 patterns shrink |
| `MONSTER_CHECK_EMBED=1`, `MONSTER_LEGACY_EMBED=1` | cross-check / old embedding search | testing only |
| `MONSTER_PHASE_SEED=S` | unit mode: pseudo-random initial phases (variance probe) | ~15% spread on d=10 units vs 150x between units: the tail is not solver variance |
| `MONSTER_REDUCE_DROP=P` | drop P% of the local learnt tier at each reduction (default 50; **unit mode now uses 90**) | **1.8x on the paired d=10 sample** (secs 0.554, CI 0.49-0.62, conflicts 1.05); 95% 82 s / 98% 104 s / 100% 178 s vs 90% 90 s on the hard unit (7,2559) |
| `monster cover-aut --d D --covers DIR [--tasks tasks.jsonl]` | symmetry group orders of a stage's generalisations (and per task) | d=10: almost all trivial; symmetric learning inside units closed (RESULTS 2026-10-27 ~11:40) |
| `glue --unit-budget B --cube-budget B` | unit mode: cube-and-conquer inside one solver after B conflicts (lookahead splits, failed literals learned); **unit-mode default is now 5000/5000** (`--cube-budget 0` restores whole-unit CDCL; other modes keep 20000/0) | **3.7x on the paired d=10 sample** (secs 0.268, CI 0.20-0.43; conflicts 0.53, CI 0.44-0.72; verdicts agree); 1.3-2.3x on three single units at B = 5k-20k; `--vivify` on top is neutral (ratio 1.03, CI 0.93-1.14) |
| `glue --biclique` (unit mode) | SBVA-style biclique reencoding of the unit CNF with definition variables (`cover::build_gamma_opts`); uncertified until the checker knows definitions, refused with `--check-every > 0` | **closed: 1.7-9x slower** in every variant (RESULTS 2026-10-28 ~15:20) |
| `glue --degree-axioms` (unit mode) | red-degree window [7,13] of every vertex as cardinality constraints (`cover::unit_degree_axioms`, aux vars); underived, so refused with `--check-every > 0` | **closed: 32x slower** on the first 12 units of the paired d=12 sample (188 s vs 6,083 s; RESULTS 2026-10-27 ~19:30) |
| `glue --book-axioms` | two-root lemmas as cardinality constraints (pair mode) | -21% conflicts, 21x slower |
| `glue --sched static` | static task schedule (reproducible per-task counts) | used by `monster ab` |
| `glue --shard I/N` | run only the tasks with index I mod N of the plan (one shard per machine; `complete` is never claimed by a shard). Merge: concatenate the shards' tasks.jsonl into one `--out` dir and run the same command without `--shard` with `--resume`: it re-solves nothing, re-runs uncertified lines, and writes the certified summary | 3-shard d=7 test: 3+3+2 tasks, merged 71/71 pairs certified in 0.1 s (2026-10-27) |
| `scripts/bundle.sh OUT.tar.gz` | self-contained worker bundle (binary, catalogues, covers, `run_shard.sh D I N [WORKERS]`) for `--shard` runs on other machines | 56 MB; d=7 shard tested from the extracted bundle (2026-10-27) |
| `glue --mode cone`, `monster cone`, `MONSTER_CONE=deg,mac` | feasible-cone search per catalogue pair (uncertified prototype, no proofs) | negative: >= 175x slower than CDCL on a d=8 pair with every option set |
| `MONSTER_CONEPROP=1` (`=nodeg`), `monster cone --cdcl` | cone reasoning as a CDCL propagator in pair mode (uncertified, refuses `--check-every`) | negative: -11% conflicts on d=10 pairs (-45% to +10%), 2-8x slower |
| `ab --base-args/--cand-args`, `--base-env/--cand-env` | per-side options / environment for A/B runs | |

## Backups and hand-off
- Every file is snapshotted to branch `backup/auto` (ungated) by `scripts/snapshot.sh`: from Claude Code hooks, and
  every 10 minutes once `scripts/install_backups.sh` has been run. All Claude conversations are exported to `context/chats/`.
- At the end of every Claude turn, a Stop hook commits everything to `main`, but only if the build, the tests
  (including the regression gate `tests/regression.rs`) and, for Lean changes, `lake build` pass, and only once
  CONTINUE.md describes the code change.
- `CLAUDE.md` holds the rules and the start-of-session checklist; `CONTINUE.md` holds the state and next steps.
- Long or memory-heavy jobs: `scripts/capped.sh NAME 40G CMD...` (own systemd unit with a memory cap). These units
  do not survive a reboot; CONTINUE.md's newest hand-off ("5-LATEST") lists the exact commands to restart them.

## Ground rules
- **Exact only.** No clause is ever added unless it is implied by F (proved), or justified by the symmetry rule
  (F is invariant under vertex permutations, and under colour swap when s = t).
- Unproved symmetry breaking (lex axioms, unlogged predicates) is never mixed with pattern images; that would be
  unsound. See IDEAS.md.
- A claim counts only when its proof checks: Lean checker (gold), Rust reference checker (fast), symmetric checker, or,
  for pair and unit gluing tasks, the independent LRAT hint checker (`HintChecker`, linear in the proof; since
  2026-10-27 certification costs ~10% of the solve instead of 65x).

## Files
| path | what |
|---|---|
| `src/pattern.rs` | pattern store, canonical forms, embedding search (the symmetric-learning engine) |
| `src/full.rs` | full formula, lemma library, SLRAT writer, reference checkers |
| `src/sat/solver.rs` | CDCL core (LRAT hints, assumptions, cores, vivification, pattern hook) |
| `verified/MonsterVerified/*.lean` | Lean: semantics (Basic), clause generation (Gen), LRAT step (Rup), symmetry rule (Image), checker + main theorem (Checker), parser, theorems |
| `RESULTS.md`, `IDEAS.md` | measurements and verdicts, ideas with soundness analysis |
| `CONTINUE.md` | how to pick the work up (for people and for Claude) |
| `CLAUDE.md` | rules and start-of-session checklist for Claude (linked from `~/CLAUDE.md`) |
| `context/` | every Claude conversation exported as Markdown (`INDEX.md` lists them) |
| `src/lift.rs` | lift rule: test proofs, checker mutant battery, SLRAT → Lean converter |
| `tests/regression.rs` | regression gate: headline results stay solved, verified and under conflict ceilings |
| `scripts/` | `snapshot.sh`, `autocommit_hook.sh`, `session_brief.sh`, `capped.sh`, `install_backups.sh`, `progress.sh` |
| `bench/progress.jsonl` | progress suite rows (`scripts/progress.sh`) |

Origin: rebuilt from the ideas on the `ramsey-*` branches of `lioncash3k6-ux/cascade-solver` (v4–v11 gluing work).
Code written with Claude (Anthropic).
