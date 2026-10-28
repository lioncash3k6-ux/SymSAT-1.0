//! Regression gate for the headline results: each must stay solved, its SLRAT proof must pass the reference checker
//! (and the Lean checker when it is built), and its conflict count must stay under a ceiling. Conflict counts are
//! deterministic, so a ceiling catches slowdowns like the stars-only one from commit 1a60950 (R(4,4)/K18 went from
//! 599 to 2,607 conflicts unnoticed). A single run says little about a chaotic solver (R(4,4)/K18 inline spans
//! 14–27,272 conflicts over relabellings), so each instance runs at relabel seeds 0–3 and the gate is on the worst of
//! them. Ceilings are about 1.5x the worst count measured on 2026-10-26 with the default flags (`--patterns --lemmas`,
//! `--lib lift`); lower them when results improve. The Stop hook (scripts/autocommit_hook.sh) commits code to main only
//! when `cargo test --release` passes.

use std::path::{Path, PathBuf};
use std::process::Command;

const SEEDS: [u32; 4] = [0, 1, 2, 3];

fn monster(args: &[&str]) -> String {
    let out = Command::new(env!("CARGO_BIN_EXE_monster")).args(args).output().expect("run monster");
    String::from_utf8_lossy(&out.stdout).into_owned() + &String::from_utf8_lossy(&out.stderr)
}

fn conflicts(out: &str) -> u64 {
    let line = out.lines().find(|l| l.starts_with("RESULT ")).unwrap_or_else(|| panic!("no RESULT line:\n{out}"));
    let i = line.find("\"conflicts\":").expect("conflicts field") + "\"conflicts\":".len();
    line[i..].chars().take_while(|c| c.is_ascii_digit()).collect::<String>().parse().expect("conflict count")
}

fn proof_path(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("monster-regression-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    dir.join(name)
}

fn unsat_verified(s: u32, t: u32, n: u32, ceiling: u64) {
    let lean = Path::new(env!("CARGO_MANIFEST_DIR")).join("verified/.lake/build/bin/checker");
    let mut worst = 0;
    for seed in SEEDS {
        let proof = proof_path(&format!("R{s}{t}_K{n}_{seed}.slrat"));
        let (ss, ts, ns, rl) = (s.to_string(), t.to_string(), n.to_string(), seed.to_string());
        let args = ["full", "--s", &ss, "--t", &ts, "--n", &ns, "--patterns", "--lemmas", "--relabel", &rl, "--slrat", proof.to_str().unwrap()];
        let out = monster(&args);
        assert!(out.contains("\"result\":\"Unsat\""), "R({s},{t})/K{n} seed {seed} is no longer UNSAT:\n{out}");
        assert!(out.contains("reference checker: s VERIFIED UNSAT"), "R({s},{t})/K{n} seed {seed}: proof not verified:\n{out}");
        if lean.exists() {
            let o = Command::new(&lean).arg(&proof).output().expect("run the Lean checker");
            assert!(String::from_utf8_lossy(&o.stdout).contains("VERIFIED UNSAT"), "the Lean checker rejects R({s},{t})/K{n} seed {seed}");
        }
        let _ = std::fs::remove_file(&proof);
        worst = worst.max(conflicts(&out));
    }
    assert!(worst <= ceiling, "R({s},{t})/K{n}: worst of seeds {SEEDS:?} is {worst} conflicts, ceiling {ceiling}: performance regression");
}

#[test]
fn r33_k6_unsat() {
    unsat_verified(3, 3, 6, 20); // worst 11
}

#[test]
fn r34_k9_unsat() {
    unsat_verified(3, 4, 9, 400); // worst 267 (32-sample max 210)
}

#[test]
fn r35_k14_unsat() {
    unsat_verified(3, 5, 14, 100); // worst 56 (32-sample max 62)
}

#[test]
fn r44_k18_unsat() {
    unsat_verified(4, 4, 18, 120); // worst 62 (32-sample max 78)
}

#[test]
fn documented_quick_check() {
    // the command README.md and CONTINUE.md give; `--proof` must verify on the default library path
    let out = monster(&["full", "--s", "4", "--t", "4", "--n", "18", "--patterns", "--lemmas", "--proof"]);
    assert!(out.contains("\"result\":\"Unsat\"") && out.contains("\"proof\":\"verified\""), "documented quick check:\n{out}");
}

#[test]
fn r44_k17_witness() {
    let out = monster(&["full", "--s", "4", "--t", "4", "--n", "17", "--patterns", "--lemmas"]);
    assert!(out.contains("\"result\":\"Sat\"") && out.contains("independently VERIFIED"), "R(4,4)/K17 witness:\n{out}");
}
