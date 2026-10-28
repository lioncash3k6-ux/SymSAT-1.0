# monster: exact Ramsey gluing solver (Rust, no dependencies)

> **Picking this up?** Read [CONTINUE.md](CONTINUE.md) first: state, running jobs, ground rules, next steps.

**What formula is solved?** Always the **full, unreduced** Ramsey formula. No symmetry-breaking predicates are added.
Symmetry is used dynamically: learned clauses propagate in every vertex position, and library lemmas are *proved* from F.
Gluing and hybrid modes reduce work by an exact case split over isomorph-free catalogues (assumptions, not axioms).

## Where we are (2026-10-26, overnight)

**Main engine: pattern CDCL** on the full K_N formula. Learned clauses are stored as canonical forbidden patterns,
and all their vertex-permuted images propagate, plus a **recursive lemma library** proved inside F (stars, books,
mixed books from smaller Ramsey numbers). Full formulas solved directly, proofs verified:

| | time | conflicts |
|---|---|---|
| R(3,4)/K9 | 0.003 s | 26 |
| R(3,5)/K14 | 0.24 s | 1,136 |
| R(4,4)/K18 | 0.59 s | 890 |
| R(4,5)/K25 lemma library (degree window [7,13] proved inside F) | ~4 min once, cached, re-verified on load in ~10 s | |

**Hybrid mode**: pattern CDCL plus catalogue cubes, with shared symmetric memory across pairs. Correct and certified
on the ladder. On R(4,5) d=8 it needs about 3× fewer conflicts per pair than pair mode but is still about 100×
slower per conflict. Overnight run: results/overnight/hyb_d8.

**One-sided cubes (new, testing):** `--one-sided` fixes only the smaller catalogue side of vertex 0 and leaves the
other side free. For R(4,5) that means 2 + 313 + 12 cubes for d = 8, 10, 12 instead of 58M pairs, and the large r44
catalogues leave the trusted base. Certified ladder checks are passing so far.

**Verification**: the independent symmetric checker on every certified run; cake_lpr (formally verified) on
expanded LRAT for small cases.

**Progress tracking**: `scripts/progress.sh` appends one row per run to `bench/progress.jsonl` (fixed suite, git
commit tagged). Hourly backup: `scripts/backup.sh` via cron (commits code only if it builds and the tests pass).

### Pattern CDCL usage
```bash
monster full --s 4 --t 4 --n 18 --patterns --lemmas --proof              # solve + symmetric proof check
monster full --s 4 --t 5 --n 25 --patterns --books --library results/library_R45_K25_books.bin --budget 6000   # K25 profile
monster glue --s 4 --t 5 --n 25 --d 8 --mode hybrid --books --check-every 8 --out runs/h8   # hybrid gluing
monster full --s 3 --t 4 --n 9 --patterns --lrat out.lrat              # LRAT with images expanded (writes out.lrat.cnf)
~/deps/cake_lpr/cake_lpr out.lrat.cnf out.lrat                          # formally verified check
```
Options: `--max-k` (pattern vertices), `--max-lbd`, `--max-edges`, `--max-pats`, `--node-budget` (embedding search
per anchor), `--budget` (conflicts).

cake_lpr: `git clone https://github.com/tanyongkiam/cake_lpr && cd cake_lpr && make`. It also checks streams
through a FIFO while the solver runs (tested with CaDiCaL LRAT on a d=10 unit).

## Build

Needs Linux x86_64, a Rust toolchain and a C linker.

```bash
# Ubuntu: sudo apt install build-essential
curl -sSf https://sh.rustup.rs | sh -s -- -y --profile minimal && source ~/.cargo/env
cargo build --release          # binary: target/release/monster  (built with target-cpu=native, see .cargo/config.toml)
cargo test --release           # unit tests: solver vs brute force, RUP checker, sha256, graph6
```

The catalogues are read from `<dir>/r<s><t>/n<k>.g6`, which is the repo's `v5/catalogs` layout on branch
`ramsey-v4-algebraic`. By default monster looks for `~/cascade-solver-ramsey-v4-algebraic/v5/catalogs`; override it with
`--catalogs DIR`. Every graph is re-checked to be (s,t)-good on load, and each level's count is compared with
McKay's table. A mismatch aborts the run.

## Use

```bash
monster info                                   # what machine am I on
monster ladder                                 # regression: both sides of R(3,3)..R(3,7), R(4,4), R(4,5) d=8, all certified
monster glue --s 4 --t 5 --n 25 --d 8 --mode pair            # one degree stage, live dashboard
monster glue --s 4 --t 5 --n 25 --d 10 --mode pair --sample 32 --seed 7   # cost estimate on a random sample
monster glue --s 4 --t 5 --n 25 --out runs/r45 --resume       # full parity route (d=8,10,12), resumable
monster cnf 4 5 A.g6 B.g6 p out.cnf            # one pair CNF, byte-identical to v6/scripts/encode.py
monster glue --s 4 --t 5 --n 25 --d 10 --mode unit --covers ~/cascade-solver-ramsey-v4-algebraic/v10/covers_r2 --unit-budget 18446744073709551615
monster gamma --covers DIR --d 10 --ga 17 --gb 698 out.cnf   # dump one unit's GAMMA as DIMACS
```

Options for `glue`:

| option | meaning |
|---|---|
| `--route parity\|all` | parity: only even red degree d (needs N odd); all: every d. Default: parity if N is odd |
| `--d 8,10` | restrict to these degree stages. The verdict then speaks only about those stages, not about R(s,t) |
| `--mode pair\|stream\|unit` | engine (see below) |
| `--workers N` | default: all hardware threads |
| `--check-every K` | certify 1 task in K with the independent checker (1 = everything, 0 = none; default 64) |
| `--chunk K` | catalogue graphs per task (stream/pair) |
| `--covers DIR --gray-a G --gray-b G` | v10 cover files for unit mode (`c35_10_g6.txt`, ...) |
| `--unit-budget C` | conflicts spent on a whole unit before going pair by pair |
| `--minimize C` | stream mode: shrink cores with C-conflict probes |
| `--vivify` | learnt-clause vivification at restarts (proof-logged) |
| `--degree-axioms` | pair mode: every vertex's red degree in the window implied by the catalogue maxima |
| `--units FILE` | unit mode: only the listed `genA genB` units |
| `--out DIR` / `--resume` | per-task JSONL log, meta.json (catalogue sha256), summary.json, SAT witnesses; resume skips finished tasks |
| `--stop-on-sat` | stop at the first verified witness |

Ctrl-C stops cleanly. A task is logged only after it finishes, so `--resume` reruns unfinished ones.

## Engines

- **pair:** a fresh CDCL solver per catalogue pair on the plain pair CNF (the encode.py formula).
- **stream:** one solver per fixed graph. The other side's edges are variables, and each catalogue graph is an
  assumption set. Failed-assumption cores go into a bitmask cache and refute later graphs without solving.
- **unit:** v10 gray-edge units. GAMMA(genA, genB) is solved whole, then pair by pair under gray-edge assumptions.
  The cover files are untrusted input, and every pair is glue-checked.

Measured so far, on 16 Ivy Bridge vCPUs:

| run | pair | stream |
|---|---|---|
| R(3,7) N=23 (2,583 pairs), no certification | 12 s | 68 s |
| R(4,5) d=8 (358 pairs), no certification | 135 s | over 2× slower (stopped at 57%) |

So "every edge gray plus core cache" is a measured negative: its formula is about 10–40× the pair formula. Unit-mode
benchmarks are in progress.

## What a verdict means

- **SAT:** the pair's model is rebuilt as a full colouring of K_N and brute-force checked for red K_s and blue K_t.
  The witness is printed in graph6. This is unconditional.
- **UNSAT for R(s,t) ≤ N:** printed only when every admissible degree of the route is covered and every pair is
  refuted. It is conditional on:
  - the degree argument
  - catalogue completeness (counts equal McKay's table)
  - the pair encoder (byte-identical to the repo's encode.py)
  - the solver, for pairs not certified
- **Certified pairs:** an independent forward RUP checker (`src/sat/checker.rs`, which shares no code with the
  solver) checks every lemma in order. The pair's refuting clause must consist only of negated assumption literals
  of that pair. The glue lemma is re-checked against the independently encoded F(A,B).

## Layout

```
src/graph.rs        bitset graphs, graph6, clique search, full K_N witness check
src/catalog.rs      catalogue loading + McKay counts
src/encode.rs       pair CNF (port of encode.py), stream formula, glue check
src/cover.rs        v10 covers, GAMMA, unit glue check (with permutations)
src/sat/solver.rs   CDCL: 2WL+blockers, 1UIP+minimisation, LBD tiers, glucose restarts, assumption trail reuse, cores, lemma log
src/sat/checker.rs  independent RUP checker
src/glue.rs         stages, tasks, workers, certification
src/dash.rs         live ANSI dashboard
src/sys.rs          machine awareness (/proc)
```
