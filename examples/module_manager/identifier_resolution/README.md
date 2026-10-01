# Qualified identifier resolution

This strict regression project defines the same object and function names in
the root's `base` and `main` exports and the imported `Values::base` export.
Each reference unfolds the definition in its own export. The imported
`check` export also uses `base::k` within that module.

```sh
target/release/litex -strict -f examples/module_manager/identifier_resolution/main.lit
cargo test --release identifier_resolution_tests -- --nocapture
```

The main file preserves the former false-equality acceptance as comments and
keeps the correct equalities active. Rust regressions execute the negative
cases: an unrelated local definition cannot prove `base::k = 1` or validate
undeclared `base::ghost`. Imported function signatures are explicitly
published to the caller with `release obj def` before applications.

No trust, axioms, or abstract predicates are used.
