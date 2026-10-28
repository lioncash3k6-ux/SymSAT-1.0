//! Machine awareness: what box are we on, and what is this process costing it right now.

use std::fs;

#[derive(Clone, Debug)]
pub struct Machine {
    pub model: String,
    pub threads: usize,
    pub mem_total_kb: u64,
    pub flags: Vec<&'static str>,
    pub hypervisor: bool,
}

pub fn machine() -> Machine {
    let cpu = fs::read_to_string("/proc/cpuinfo").unwrap_or_default();
    let model = cpu
        .lines()
        .find(|l| l.starts_with("model name"))
        .and_then(|l| l.split(':').nth(1))
        .map(|s| s.trim().to_string())
        .unwrap_or_else(|| "unknown cpu".into());
    let flag_line = cpu.lines().find(|l| l.starts_with("flags")).unwrap_or("");
    let have: std::collections::HashSet<&str> = flag_line.split_whitespace().collect();
    let mut flags = Vec::new();
    for f in ["popcnt", "avx", "avx2", "bmi2", "avx512f"] {
        if have.contains(f) {
            flags.push(f);
        }
    }
    let threads = std::thread::available_parallelism().map(|n| n.get()).unwrap_or(1);
    Machine {
        model,
        threads,
        mem_total_kb: meminfo("MemTotal"),
        flags,
        hypervisor: have.contains("hypervisor"),
    }
}

pub fn meminfo(key: &str) -> u64 {
    fs::read_to_string("/proc/meminfo")
        .unwrap_or_default()
        .lines()
        .find(|l| l.starts_with(key))
        .and_then(|l| l.split_whitespace().nth(1))
        .and_then(|v| v.parse().ok())
        .unwrap_or(0)
}

/// (current RSS kB, peak RSS kB) of this process.
pub fn rss_kb() -> (u64, u64) {
    let st = fs::read_to_string("/proc/self/status").unwrap_or_default();
    let get = |k: &str| {
        st.lines()
            .find(|l| l.starts_with(k))
            .and_then(|l| l.split_whitespace().nth(1))
            .and_then(|v| v.parse().ok())
            .unwrap_or(0)
    };
    (get("VmRSS:"), get("VmHWM:"))
}

/// Total user+system CPU seconds consumed by this process.
pub fn cpu_seconds() -> f64 {
    let st = fs::read_to_string("/proc/self/stat").unwrap_or_default();
    // fields after the ")" of the comm field; utime and stime are fields 14 and 15 (1-based)
    let rest = st.rsplit(')').next().unwrap_or("");
    let f: Vec<&str> = rest.split_whitespace().collect();
    let ticks = 100.0; // CLK_TCK is 100 on Linux x86_64
    if f.len() > 13 {
        let u: f64 = f[11].parse().unwrap_or(0.0);
        let s: f64 = f[12].parse().unwrap_or(0.0);
        (u + s) / ticks
    } else {
        0.0
    }
}

pub fn loadavg() -> String {
    fs::read_to_string("/proc/loadavg")
        .unwrap_or_default()
        .split_whitespace()
        .take(3)
        .collect::<Vec<_>>()
        .join(" ")
}
