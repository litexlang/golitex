# Litex Examples

This directory separates reader-facing examples from developer-only fixtures,
regressions, drafts, and proof journals. For the complete tutorial, start with
[`docs/Examples.md`](../docs/Examples.md); use this page when you want a runnable
file for a particular kind of behavior.

## Public Reading Path

1. [`01_proof_patterns/`](01_proof_patterns/) contains small proof-control and
   theorem-reuse patterns.
2. [`02_builtin_math/`](02_builtin_math/) shows arithmetic, order, finite-set,
   function, and numeric rules provided by the verifier.
3. [`03_language_features/`](03_language_features/) covers definitions,
   settings, structs, well-definedness, and imports.
4. [`04_case_studies/`](04_case_studies/) contains larger worked proofs built
   from several interfaces.
5. [`05_compiler_interop/`](05_compiler_interop/) records Litex-to-Lean
   compiler acceptance examples and current boundaries.
6. [`08_module_repository/`](08_module_repository/) is a configured module
   project that demonstrates ordered exports and submodules.

The numbering is a reading order, not a requirement that every number exist.
Public `.lit` files should have descriptive names and remain independently
runnable unless their purpose is specifically to demonstrate a configured
module or import.

## Developer Material

[`_internal/`](_internal/) contains named regression fixtures, imported module
fixtures, exploratory drafts, generated To-Lean work, and historical proof
journals. These files may be useful to maintainers, but they are not the
recommended reader entry point.

`tmp.lit` is the single repository scratch entrypoint retained for quick local
experiments. Do not add `tmp1.lit`, `tmp2.lit`, or other unnamed root examples;
graduate useful work into a descriptive public or `_internal/` path. The main
examples harness deliberately excludes `tmp.lit`.

## Verification

Run one standalone file with the release runner:

```text
target/release/litex -compact -isolated -runner -f examples/02_builtin_math/fundamental_comparison_builtin_rules.lit
```

Run the configured module example with:

```text
target/release/litex -compact -runner -r examples/08_module_repository
```

Run the examples and executable documentation harness with:

```text
cargo test --release run_examples -- --nocapture
```
