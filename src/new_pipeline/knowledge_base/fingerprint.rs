//! Content-addressed fingerprint for a module's KB artifact.
//!
//! Stable FNV-1a 64 over ABI + config + ordered export bytes + dep fingerprints.
//! Not cryptographic; only for cache invalidation.

use super::paths::KB_ABI;
use std::fmt::Write as _;

/// Inputs the caller gathers from the module tree (KB does not walk Runtime).
pub struct FingerprintInputs<'a> {
    pub litex_config_bytes: &'a [u8],
    /// `(relative_export_path, file_bytes)` in `[export]` order.
    pub export_files: &'a [(String, Vec<u8>)],
    /// Already-computed fingerprints of direct imported deps (sorted by path).
    pub dep_fingerprints: &'a [String],
}

pub fn compute_fingerprint(inputs: &FingerprintInputs<'_>) -> String {
    let mut h = Fnv64::new();
    h.write(b"litex-kb-abi:");
    h.write(KB_ABI.as_bytes());
    h.write(&[0]);
    h.write(b"config:");
    h.write(inputs.litex_config_bytes);
    h.write(&[0]);
    h.write(b"exports:");
    for (path, bytes) in inputs.export_files {
        h.write(path.as_bytes());
        h.write(&[0]);
        h.write(&(bytes.len() as u64).to_le_bytes());
        h.write(bytes);
        h.write(&[0]);
    }
    h.write(b"deps:");
    for dep in inputs.dep_fingerprints {
        h.write(dep.as_bytes());
        h.write(&[0]);
    }
    let mut out = String::new();
    let _ = write!(&mut out, "{:016x}", h.finish());
    out
}

struct Fnv64 {
    state: u64,
}

impl Fnv64 {
    fn new() -> Self {
        Self {
            state: 0xcbf29ce484222325,
        }
    }

    fn write(&mut self, bytes: &[u8]) {
        for &b in bytes {
            self.state ^= u64::from(b);
            self.state = self.state.wrapping_mul(0x100000001b3);
        }
    }

    fn finish(self) -> u64 {
        self.state
    }
}
