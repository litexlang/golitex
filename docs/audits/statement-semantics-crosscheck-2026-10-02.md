# Statement semantics cross-check (2026-10-02)

This is a focused review of the 50 reachable `Stmt` leaves, not a proof of soundness for every verifier rule. I compared the current [statement inventory](../../src/ast/stmt.rs), [Manual](../Manual.md), the [statement regression suite](../../examples/test_statements/README.md), and legacy commit `8ebce3f7a4a4c61250063c9eb9e69c9fb3cfa735` (its old `src/`, excluding `src/new_pipeline`). The working tree was changing during review. Runtime observations below use a copied release binary with SHA-256 `83aab093ead837bbe4710db5690d06c7ededac54937308fff1a30c207e3c3514`, invoked with `-strict -f` and checked for process status, JSON `success`, `session_error`, and per-statement outcomes. A subsequent edit requires a new replay.

The [suite runner](../../examples/test_statements/run.py) exercised 361 checks over all 50 leaves with this binary: 360 matched their current expectations. The one mismatch, K004 (recursive call under addition), **now succeeds** although its gap record expects failure; that is a stale expectation after concurrent implementation work, not a new rejection. The other 11 gap reproductions matched their recorded failing behavior. The [issue index](../../examples/test_statements/bugs/README.md) has exact fixtures and controls for K001–K010, including both variants of K007 and K009.

Subsequent statement-boundary repair: the user requested strict-template rejection,
conditional finite-set enumeration, nested by proof methods, and source WD before
eval. Those routes now have [acceptance evidence](../../examples/test_statements/experience/problem_notes/statement-boundary-repairs.md).
Cartesian-domain enumeration remains explicitly unsupported by user decision;
the Manual promise was narrowed. The discrepancies below describe the original
binary checkpoint above and are retained as historical evidence.

## High-risk behavior now correct

`by def` does **not** simply ask the general verifier to accept its target. [Its executor](../../src/execute/execute_by_stmt/exec_by_def_stmt.rs) calls `search_atomic_except_equality_fact_proof_by_definition` even if the fact is already known, and then stores the fact only after that route succeeds. The current binary accepts:

```litex
prop is_zero(x R):
    x = 0
by def $is_zero(0)
```

It rejects `by def 1 > 0`, while the ordinary arithmetic fact may be provable. This agrees with [Manual § Explicit definitions and `by def`](../Manual.md#explicit-definitions-and-by-def-preview). A qualified predicate also resolves its owning definition: the cross-module `obtain` shadowing probe now rejects its attempted `a = 1` and `0 = 1`, and [the owning-definition regression](../../tests/unit/execute/declaration_bindings/tests.rs) covers this boundary.

The earlier [soundness audit](statement-soundness-2026-10-01.md) identified four false-proof routes. Replaying its invalid theorem arguments, existential witness types, predicate argument types, and unstructured induction examples against this binary gives rejection at the owning statement, with ordinary false facts rejected as controls. The legacy unstructured induction had the same mixed base/induction-hypothesis scope, so that particular fault was inherited, rather than introduced by migration. The previous false-proof output must be rechecked with the repaired verifier before use.

## Current discrepancies

### 1. `-strict` misses `trust have` inside a template (trust boundary)

<!-- litex:skip-test -->
```litex
template<S set>:
    trust have fabricated R:
        fabricated = 0
```

This complete file exits 0 under `-strict`. A top-level `trust have` control is rejected. [The top-level strict gate](../../src/execute/exec_stmt.rs) sees only `Stmt::Definition(DefTemplateStmt)`, while [template execution](../../src/execute/execute_def_template_stmt/exec_def_template_stmt.rs) calls `exec_trust_have_stmt` directly and [that executor](../../src/execute/execute_unsafe_stmt/exec_trust_have_stmt.rs) has no strict check. Legacy `exec_trust_have_stmt` checked strict mode at its own entry (`src/execution/trust_execution/parameterized_assumptions.rs` at the pinned commit). This conflicts with [Manual § Trust boundary](../Manual.md#trust-boundary). The exact source and controls are in [K006](../../examples/test_statements/bugs/def_template_stmt/K006-strict-template-trust-have/README.md). The observed violation is acceptance of the trusted template declaration; this probe alone does not show a downstream false theorem.

### 2. Finite enumeration loses conditional antecedents and Cartesian carriers (incomplete proofs)

<!-- litex:skip-test -->
```litex
by enumerate finite_set:
    ? forall x {0, 1}:
        x = 1
        =>:
            x = 1
```

Both `by enumerate finite_set` and `by for` reject this true conditional goal; the standalone `forall` control succeeds. [The shared enumerator](../../src/execute/execute_by_stmt/enumerate_forall.rs) verifies each instantiated `then_fact` without using or deciding `dom_facts`. Legacy enumeration and iteration first checked each instantiated domain fact, assumed it when true, and skipped a case only after proving its negation (`src/execution/proof_directives/{enumeration,iteration}.rs` at the pinned commit). See [K009](../../examples/test_statements/bugs/by_enumerate_finite_set_stmt/K009-conditional-enumeration-goal/README.md).

<!-- litex:skip-test -->
<!-- litex:skip-test -->
```litex
by for:
    ? forall p cart({0, 1}, {2, 3}):
        p = p
```

This also rejects. [Domain resolution](../../src/execute/execute_by_stmt/enumerate_helpers.rs) accepts literal list sets and numeric ranges only. Legacy `ByForExpansion::CartOfListSets` handled finite products, and [the Manual](../Manual.md#finite-enumeration-and-range-expansion) still advertises them. See [K008](../../examples/test_statements/bugs/by_for_stmt/K008-finite-cartesian-domain/README.md). These are false rejections, not observed false proofs. Repairs need negative controls for false conclusions under true premises and for nonfinite domains.

### 3. Nested proof methods in `by` blocks have a migration compatibility gap

<!-- litex:skip-test -->
```litex
by extension:
    ? {1} = {1}
    by def {1} $subset {1}
```

The current parser accepts the block but the executor rejects the nested `by def`; the bodyless `by extension {1} = {1}` control succeeds. [The shared proof-body helper](../../src/execute/execute_by_stmt/helper.rs) accepts only `Stmt::Fact`, and `by extension`, `by fn_extension`, cases, contradiction, finite enumeration, and other methods call it. Legacy extension and enumeration used full `execute_statement` for nested proof steps. The [Manual example](../Manual.md#finite-enumeration-and-range-expansion) explicitly labels its nested extension proof a retained migration example that does not currently verify, so this is a known compatibility gap rather than a claim that the Manual promises current success. Re-enabling general statements requires careful child-scope and trust-gate handling, especially in light of item 1.

### 4. `eval` does not check the input expression's domain (command behavior)

<!-- litex:skip-test -->
<!-- litex:skip-test -->
```litex
algo identity(x N) N by cases:
    case x = x: x
eval identity(-1)
```

This exits 0. [Current `exec_eval_stmt`](../../src/execute/execute_eval_stmt/exec_eval_stmt.rs) rewrites and evaluates the expression without a well-definedness check; legacy `evaluate_obj_for_eval_stmt` called `verify_obj_well_defined_result` first. `eval` stores no mathematical fact, so the observation is a domain-misleading evaluation result, not a false proof. The [Manual's statement index](../Manual.md#statement-index) says only that the expression must belong to the supported executable subset; whether evaluation should enforce the callable's mathematical domain is a product-semantic decision before changing this command.

## Documented semantics that may surprise users

At the time of this audit, `by thm t(args) => fact` applied the theorem inside a child environment and asked the **ordinary atomic verifier** to prove `fact` there. Thus the following succeeded even though the target was independently provable and unrelated to `t`:

<!-- litex:skip-test -->
```litex
thm irrelevant:
    ? 1 = 1
by thm irrelevant => 2 = 2
```

The [Manual § Named interfaces](../Manual.md#named-interfaces-thm-axiom-release-thm-and-by-thm--fact) at that checkpoint explicitly permitted a target that was not a direct theorem conclusion. This was a provenance/interface choice under the then-documented rule. At the time of this audit, `-strict` intentionally still permitted named `axiom` and set-theoretic releases; the template bypass above was different because strict explicitly promised to reject `trust have`.

Update, 2026-10-06: selected theorem calls now require a directly returned atomic
conclusion. The historical example above is rejected; the Manual has been
updated. See the [strict-selection tracer](../../examples/stmt_nodes/by/by_thm_strict_selection.lit).

Update, 2026-10-05: strict mode now also rejects user `axiom` declarations.
Named foundation releases remain allowed. See the [source-owned acceptance](../../examples/test_statements/experience/problem_notes/strict-user-axiom-2026-10-05.md).

This review did not edit the kernel or change any statement contract. The per-statement suite is strong coverage of entry points and regression behavior; it does not establish that every supported proposition or every nested environment transition is sound.
