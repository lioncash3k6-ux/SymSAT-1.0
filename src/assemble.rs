//! `monster assemble-spec`: the UNTRUSTED input of `checker --assemble SPEC` (verified/MonsterVerified/Assemble.lean).
//! For one gluing stage d it writes, next to the spec, one hint per catalogue graph (its generalisation in the cover
//! and the relabelling σ = pi⁻¹ of the cover's `A` line, so that `relabel σ false X` is the instantiation the unit
//! clause was proved for) and appends a `stage d` block to the spec naming the two graph6 files (with McKay's counts
//! as a decoder cross-check), the unit grid (nA x nB), the hint files, and the clause source: `--from-record FILE` → `record FILE` (written
//! by `checker --lemmas --record`, i.e. by `unit-lean-stage`), `proofs LIST` (SLRAT files verified in-process by the
//! assembler: the hypothesis-free form), or `fakerecord FILE` (the exact unit clauses, unverified: timing runs only).
//! Nothing here is trusted: every hint and clause is checked by the Lean Bool `stageOK`; a wrong hint makes it fail.

use crate::catalog::Level;
use crate::cover::Cover;
use crate::glue::Stage;
use crate::leanunit::assumption_lits;
use std::fmt::Write as _;
use std::path::{Path, PathBuf};

pub enum Source {
    Record(PathBuf),
    Proofs(PathBuf),
    Fake,
}

fn abs(p: &Path) -> String {
    std::fs::canonicalize(p).map(|x| x.display().to_string()).unwrap_or_else(|_| p.display().to_string())
}

/// hint lines for one side: catalogue index -> `gen σ0 .. σ{n-1}` with σ = pi⁻¹
fn hints(cov: &Cover, ncat: usize, n: usize) -> Result<String, String> {
    let mut lines: Vec<Option<String>> = vec![None; ncat];
    for (g, members) in cov.members.iter().enumerate() {
        for m in members {
            let mut sigma = vec![usize::MAX; n];
            for a in 0..n {
                let u = m.pi[a] as usize;
                if u >= n || sigma[u] != usize::MAX {
                    return Err(format!("catalogue graph {}: pi is not a permutation", m.cat));
                }
                sigma[u] = a;
            }
            let mut s = g.to_string();
            for u in 0..n {
                let _ = write!(s, " {}", sigma[u]);
            }
            lines[m.cat as usize] = Some(s);
        }
    }
    let mut out = String::new();
    for (i, l) in lines.into_iter().enumerate() {
        out.push_str(&l.ok_or_else(|| format!("catalogue graph {i} is in no generalisation"))?);
        out.push('\n');
    }
    Ok(out)
}

pub fn write_spec(st: &Stage, d: usize, out_dir: &Path, spec: &Path, source: Source, threads: usize) -> Result<(), String> {
    let (ca, cb) = (st.cov_a.as_ref().ok_or("no A cover")?, st.cov_b.as_ref().ok_or("no B cover")?);
    write_spec_parts(&st.a, &st.b, ca, cb, d, out_dir, spec, source, threads)
}

/// the same from the parts (catalogue levels and covers of the two sides)
#[allow(clippy::too_many_arguments)]
pub fn write_spec_parts(a: &Level, b: &Level, ca: &Cover, cb: &Cover, d: usize, out_dir: &Path, spec: &Path, source: Source, threads: usize) -> Result<(), String> {
    std::fs::create_dir_all(out_dir).map_err(|e| format!("{}: {e}", out_dir.display()))?;
    let (na, nb) = (ca.gens.len(), cb.gens.len());
    let ha = out_dir.join(format!("hintA_d{d}.txt"));
    let hb = out_dir.join(format!("hintB_d{d}.txt"));
    std::fs::write(&ha, hints(ca, a.graphs.len(), a.n)?).map_err(|e| format!("{}: {e}", ha.display()))?;
    std::fs::write(&hb, hints(cb, b.graphs.len(), b.n)?).map_err(|e| format!("{}: {e}", hb.display()))?;
    let src = match source {
        Source::Record(p) => {
            // a file, or a directory of `*.rec` files (one per Lean batch of `unit-lean-stage`): one `record` line each
            if p.is_dir() {
                let mut files: Vec<PathBuf> = std::fs::read_dir(&p)
                    .map_err(|e| format!("{}: {e}", p.display()))?
                    .filter_map(|e| e.ok().map(|e| e.path()))
                    .filter(|q| q.extension().is_some_and(|x| x == "rec"))
                    .collect();
                files.sort();
                if files.is_empty() {
                    return Err(format!("{}: no .rec files", p.display()));
                }
                files.iter().map(|q| format!("record {}", abs(q))).collect::<Vec<_>>().join("\n")
            } else {
                format!("record {}", abs(&p))
            }
        }
        Source::Proofs(p) => format!("proofs {}", abs(&p)),
        Source::Fake => {
            let p = out_dir.join(format!("fake_d{d}.rec"));
            let mut s = String::new();
            for (ga, ga_gen) in ca.gens.iter().enumerate() {
                for (gb, gb_gen) in cb.gens.iter().enumerate() {
                    let _ = write!(s, "u{ga}_{gb}");
                    for l in assumption_lits(ga_gen, gb_gen) {
                        let _ = write!(s, " {}", -l);
                    }
                    s.push('\n');
                }
            }
            std::fs::write(&p, s).map_err(|e| format!("{}: {e}", p.display()))?;
            format!("fakerecord {}", abs(&p))
        }
    };
    let block = format!(
        "stage {d}\ncatA {}\ncatB {}\ncountA {}\ncountB {}\nnA {na}\nnB {nb}\nhintA {}\nhintB {}\n{src}\nthreads {threads}\n",
        abs(&a.path),
        abs(&b.path),
        a.mckay.map(|c| c.to_string()).unwrap_or_else(|| a.graphs.len().to_string()),
        b.mckay.map(|c| c.to_string()).unwrap_or_else(|| b.graphs.len().to_string()),
        abs(&ha),
        abs(&hb)
    );
    use std::io::Write;
    let mut f = std::fs::OpenOptions::new().create(true).append(true).open(spec).map_err(|e| format!("{}: {e}", spec.display()))?;
    f.write_all(block.as_bytes()).map_err(|e| e.to_string())?;
    println!(
        "assemble-spec d={d}: {} A-graphs (K_{}) in {na} generalisations, {} B-graphs (K_{}) in {nb}; {} units; appended to {}",
        a.graphs.len(),
        a.n,
        b.graphs.len(),
        b.n,
        na * nb,
        spec.display()
    );
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::leanstage::{run_stage, StageOpts};

    /// THE SMALL END-TO-END ASSEMBLY: the whole R(4,5) d=7 stage (8 units, real covers and catalogues) through
    /// `unit-lean-stage` (files kept, clauses recorded by `checker --lemmas --record`), then `checker --assemble`
    /// in both forms: the record form (`stageRefuted_of_record`) and the in-process form (`stageRefuted_of_verified`,
    /// every proof re-verified by the assembler itself, no hypothesis beyond the catalogue files); a record with one
    /// flipped literal must be rejected. Runs when the checker, the covers and the catalogues are present.
    #[test]
    fn assemble_d7_record_and_in_process() {
        let lean = std::path::Path::new("verified/.lake/build/bin/checker");
        let covers = std::path::Path::new("results/covers_r45");
        let catdir = crate::catalog::default_dir();
        if !lean.exists() || !covers.exists() || !catdir.join("r35/n7.g6").exists() {
            return;
        }
        let probe = std::process::Command::new(lean).output().unwrap();
        if !String::from_utf8_lossy(&probe.stdout).contains("--assemble") {
            return; // a checker without the mode
        }
        let a = crate::catalog::load(&catdir, 3, 5, 7).unwrap();
        let b = crate::catalog::load(&catdir, 4, 4, 17).unwrap();
        let ca = Cover::load(&covers.join("c35_7_g6.txt"), &a.graphs).unwrap();
        let cb = Cover::load(&covers.join("c44_17_g6.txt"), &b.graphs).unwrap();
        let dir = std::env::temp_dir().join(format!("monster-assemble-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        let opts = StageOpts { out: dir.clone(), workers: 3, batch: 8, keep: true, lean: lean.to_path_buf(), resume: false, budget: u64::MAX, lean_jobs: 2, cube_budget: 5_000, shard: None };
        let tt = run_stage(4, 5, 25, 7, &ca.gens, &cb.gens, &opts, true).unwrap();
        assert_eq!((tt.units, tt.verified, tt.failed), (8, 8, 0));
        let rec = dir.join("rec");
        let mut rec_lines = 0;
        for e in std::fs::read_dir(&rec).unwrap() {
            rec_lines += std::fs::read_to_string(e.unwrap().path()).unwrap().lines().count();
        }
        assert_eq!(rec_lines, 8, "one record line per verified unit");
        let run = |spec: &Path| -> (i32, String) {
            let out = std::process::Command::new(lean).arg("--assemble").arg(spec).output().unwrap();
            (out.status.code().unwrap_or(-1), String::from_utf8_lossy(&out.stdout).to_string())
        };
        // record form
        let spec_r = dir.join("record.spec");
        write_spec_parts(&a, &b, &ca, &cb, 7, &dir, &spec_r, Source::Record(rec.clone()), 4).unwrap();
        let (code, out) = run(&spec_r);
        assert!(out.contains("s STAGE 7 REFUTED GIVEN THE RECORD") && code == 0, "record form: {out}");
        // in-process form: the assembler verifies the 8 kept proof files itself
        let list = dir.join("proofs.txt");
        let mut body = String::new();
        for e in std::fs::read_dir(dir.join("units")).unwrap() {
            body.push_str(&format!("{}\n", e.unwrap().path().display()));
        }
        assert_eq!(body.lines().count(), 8, "files kept");
        std::fs::write(&list, body).unwrap();
        let spec_p = dir.join("proofs.spec");
        write_spec_parts(&a, &b, &ca, &cb, 7, &dir, &spec_p, Source::Proofs(list), 4).unwrap();
        let (code, out) = run(&spec_p);
        assert!(out.contains("s STAGE 7 REFUTED: StageRefuted") && out.contains("stageRefuted_of_verified") && code == 0, "in-process form: {out}");
        // mutant record: one literal of the first clause flipped
        let mut lines: Vec<String> = Vec::new();
        for e in std::fs::read_dir(&rec).unwrap() {
            lines.extend(std::fs::read_to_string(e.unwrap().path()).unwrap().lines().map(String::from));
        }
        let mut tk: Vec<String> = lines[0].split_whitespace().map(String::from).collect();
        tk[3] = format!("{}", -tk[3].parse::<i64>().unwrap());
        lines[0] = tk.join(" ");
        let mrec = dir.join("mutant.rec");
        std::fs::write(&mrec, lines.join("\n") + "\n").unwrap();
        let spec_m = dir.join("mutant.spec");
        write_spec_parts(&a, &b, &ca, &cb, 7, &dir, &spec_m, Source::Record(mrec), 4).unwrap();
        let (code, out) = run(&spec_m);
        assert!(out.contains("s STAGE 7 NOT REFUTED") && code == 1, "mutant: {out}");
        let _ = std::fs::remove_dir_all(&dir);
    }
}

/// `monster merge-shards --out DIR SHARD_DIR...`: concatenate the shards' `verified.jsonl` into `DIR/verified.jsonl`
/// (then the stage command with `--resume` skips every verified unit and writes `summary.json`) and copy every
/// `rec/*.rec` into `DIR/rec/` with a shard-unique name (`assemble-spec --from-record DIR/rec`).
pub fn merge_shards(out: &Path, shards: &[PathBuf]) -> Result<(), String> {
    use std::io::Write;
    std::fs::create_dir_all(out.join("rec")).map_err(|e| format!("{}: {e}", out.display()))?;
    let mut jsonl = std::fs::OpenOptions::new().create(true).append(true).open(out.join("verified.jsonl")).map_err(|e| e.to_string())?;
    let (mut units, mut recs) = (0usize, 0usize);
    for (k, sh) in shards.iter().enumerate() {
        let text = std::fs::read_to_string(sh.join("verified.jsonl")).map_err(|e| format!("{}: {e}", sh.join("verified.jsonl").display()))?;
        for line in text.lines().filter(|l| l.contains("\"lean\":true")) {
            writeln!(jsonl, "{line}").map_err(|e| e.to_string())?;
            units += 1;
        }
        if let Ok(rd) = std::fs::read_dir(sh.join("rec")) {
            for e in rd.flatten() {
                let p = e.path();
                if p.extension().is_some_and(|x| x == "rec") {
                    let name = format!("shard{k}_{}", p.file_name().unwrap().to_string_lossy());
                    std::fs::copy(&p, out.join("rec").join(name)).map_err(|e| format!("{}: {e}", p.display()))?;
                    recs += 1;
                }
            }
        }
    }
    println!("merge-shards: {units} verified units from {} shards appended to {}, {recs} record files in {}", shards.len(), out.join("verified.jsonl").display(), out.join("rec").display());
    Ok(())
}
