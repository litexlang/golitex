# Function-family binding and owner acceptance

Task: repair Mechanics B11–B13 and related qualified-predicate projection after the 2026-10-02 user approval.

Run the local declaration tracer as StandaloneFile, RootExport (`local.lit`) and ImportedExport (Rust fixture / library probes), and run `main.lit` for actual cross-module ownership:

```sh
target/release/litex -strict -f examples/stmt_nodes/definition/local_function_family_bindings.lit
target/release/litex -strict -f examples/module_manager/function_family_bindings/local.lit
target/release/litex -strict -f examples/module_manager/function_family_bindings/main.lit
cargo test --release declaration_binding_tests
```

Require exit 0, JSON success true and no session_error for positive CLI gates. Rust regressions separately reject foreign R-to-N recursion, the template false-value bridge, incorrect qualified witnesses/obtains, wrong inferred equality and wrong parameter carriers. They also check three CodeSource values, later roots, name reuse and failed-proof rollback. Qualified template/struct AST consumers have direct owner tests; their explicit qualified surface syntax remains unsupported. Cache codec still falls back to source for the other function families; this fixture does not claim warm-cache coverage for them.

The active tracer also proves `have fn f by exist!` from a source `forall f`; source binders finish before the chosen function receives its own binding. General nested shadowing remains rejected.
