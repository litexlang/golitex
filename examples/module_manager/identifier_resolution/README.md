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

The tuple containing `base::k` and `Values::base::k` has exact domain
`closed_range(1,2)`. The caller releases the two declarations' type facts,
checks `pair $in finite_seq(R,2)`, then reads `pair(1)` and `pair(2)` from their
respective exports. Rust controls reject a third position, a different length
and an equality between the two coordinates. Local and qualified forms of
the same compound application retain one canonical key.

No trust, axioms, or abstract predicates are used.
