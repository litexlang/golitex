# Axiom store example. Golden: `eq_refl.axiom.json`

Surface (Manual preview):

```litex
axiom eq_refl:
    ? forall x R:
        x = x
```

**Note:** `AxiomStmt` is parsed and this codec round-trips the AST, but
`exec_stmt` does not yet handle `DefinitionStmt::AxiomStmt` (falls through to
Unsupported → silent CLI exit 1 with `session_error`). The `.lit` documents the
intended surface; run acceptance for now is the Rust golden / round-trip tests.
Wire `exec_axiom` separately when definitions need to land in
`axiom_definitions`.
