# Strict user-axiom rejection

Maintainer-authorized policy update, 2026-10-05. Implementation, final
current-source release build and all scoped behavior checks are complete.

## Before and now

```litex
# Before: all three statements succeeded under -strict, exit 0.
# axiom wrong:
#     ? forall x R:
#         0 = 1
# by thm wrong(0) => 0 = 1
# 0 = 1

# Now: -strict rejects the declaration, exit 1, success false, no statements.
axiom wrong:
    ? forall x R:
        0 = 1
by thm wrong(0) => 0 = 1
0 = 1
```

This excerpt mirrors the executed [persistent tracer](../../../stmt_nodes/definition/strict_axiom_policy.lit).
Ordinary mode still accepts its explicit assumption and both subsequent uses.
Even a true user axiom is rejected in strict mode; the executable
[identity boundary](../../boundaries/strict-axiom-rejected.lit) covers this case.

The existing [statement-entry policy](../../../../src/execute/exec_stmt.rs)
now rejects `DefinitionStmt::AxiomStmt` with `` `axiom` is forbidden under Litex
`-strict` ``. Existing trust diagnostics are preserved. No AST fields, runtime
state, environment stores, transactions, caches or proof-search rules changed.
Pure abstract signatures, checked theorems and named foundation releases remain
allowed. Abstract predicate instances still require proof.

## Verified evidence

- Initial and final current-source release builds: passed.
- `cargo test --release --offline --lib statement_boundary_tests -- --nocapture`: 11/11. Direct and claim/thm/by/sketch axioms, true and false conclusions, rollback, same-session reuse, and existing trust behavior are covered.
- `cargo test --release --offline --lib strict_cache_tests -- --nocapture`: 4/4. Cold strict and strict after ordinary cache warmup both reject a transitive user axiom; ordinary mode actually replays its cache.
- `cargo test --release --offline --lib predicate_signature_tests -- --nocapture`: 10/10; the affected `stored_sum_equality_is_reused_with_alpha_renamed_endpoints` filter: 1/1. All four focused Cargo gates were rerun against the final current source: 26/26.
- Production per-statement runner: AxiomStmt, TrustStmt, TrustHaveStmt, DefAbstractPropStmt, DefTemplateStmt, ReleaseAxiomOfChoiceStmt, ReleaseRegularityAxiomStmt: 58/58; no unexpected failures or recorded gaps.
- Twelve public CLI controls plus help: passed. Accepted cases require exit 0, top-level `success: true`, nonempty successful statements and no session error. Forbidden assumptions require exit 1, `success: false`, the specific error and no statement results.
- Current help, Manual, CLI guide, FAQ, learner cheatsheet, README and statement-suite policy notes are synchronized. All 151 executable blocks in the five touched current Markdown guides are unchanged; no whole-docs proof migration is claimed.

Exact CLI output, commands, binary/source hashes and the retained test-binary
invocations are in [the verification receipt](../../proof_journals/strict_user_axiom_2026-10-05.json).

```sh
target/release/litex -f examples/stmt_nodes/definition/strict_axiom_policy.lit
target/release/litex -strict -f examples/stmt_nodes/definition/strict_axiom_policy.lit
python3 examples/test_statements/run.py --leaf AxiomStmt --binary target/release/litex --require-no-gaps
```

The second command intentionally rejects. The tracer is collected by
`run_examples_statement_boundary_tracers`; no whole examples, docs, kernel,
Lean, textbook or release suite is claimed.

## Transient concurrent build failure (resolved)

After the initial successful build and Cargo gates, unrelated Rust files
changed concurrently. One fresh release build and the next Cargo test
invocation temporarily failed in the new function-domain code:

```rust
// Former concurrent import in src/execute/execute_fact_stmt/function_domain.rs: E0432.
use super::well_defined_results::verify_obj::{FnObjDomainFnSetEvidence, ObjWellDefinedByDefCommonStages};
```

That import did not resolve at the time of the failed build. The projection
also lacked a newly added variant (reduced former source shape):

```rust
match &proof.source {
    CompleteFunctionDomainSourceProof::AnonymousFunction { .. } => /* existing projection */,
    CompleteFunctionDomainSourceProof::Membership { .. } => /* existing projection */,
    // ApplicationReturn is not covered: E0004.
}
```

These files were not changed by this task. After they were independently
updated, the final current-source release build, all four focused Cargo test
filters, all twelve CLI controls plus help and all 58 statement checks passed.
The receipt retains both the transient failure and final successful build;
final acceptance does not depend only on the retained earlier executables.
