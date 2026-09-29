# Memorial: legacy Litex kernel

This directory is an **archival copy** of the previous `src/` tree
(plus related legacy unit/integration tests), before the current kernel
became the sole crate root.

It is **not** part of the Rust crate:

- not declared in `lib.rs`
- not referenced by `Cargo.toml` bins/tests
- never `mod` / `use` from the live kernel

Keep for history / comparison. Safe to delete when no longer needed.
