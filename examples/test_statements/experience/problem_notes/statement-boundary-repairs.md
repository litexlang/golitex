# Statement boundary repairs

Status: scoped repairs verified on 2026-10-02.
User decisions: repair strict, finite-set conditional enumeration, nested by proof bodies,
and eval source WD. Cartesian-domain enumeration remains explicitly unsupported.

## Before and current behavior

```litex
# Previously accepted under -strict; now rejected with forbidden trust-have.
# template<S set>:
#     trust have hidden R:
#         hidden = 1
```

The common statement gate now inspects `DefTemplateStmt.template_def_stmt` for
`TemplateDefEnum::TrustHaveStmt`. It rejects before template parameters or
facts are introduced. Normal-mode template trust remains legal; existing
named-axiom policy is unchanged. No AST or Env/Runtime state representation
was changed by this task.

```litex
# Previously rejected for the zero assignment; now verified.
# by enumerate finite_set:
#     ? forall n {0, 1, 2}:
#         n > 0
#         =>:
#             n != 0
by enumerate finite_set:
    ? forall n {0, 1, 2}:
        n > 0
        =>:
            n != 0
```

Each assignment reintroduces the original binders and assumes its concrete
equalities locally. A proved negative atomic premise closes that assignment;
otherwise source-order premises are assumed locally and all conclusions must
verify. Unknown antecedents are never skipped as false. Proof-body statements
can use the binder names. False conclusions under true premises still reject.
Both `by enumerate finite_set` and `by for` share this pipeline. Displayed list
sets and existing concrete integer ranges are supported; `cart(...)` is not.
K007 and K009 are resolved; K008 is a user-selected unsupported boundary.
K010's arithmetic-carrier issue remains a separate open problem.

```litex
# Previously rejected as a non-fact body step; now verified.
# by extension:
#     ? {1} = {1}
#     by def {1} $subset {1}
by extension:
    ? {1} = {1}
    by def {1} $subset {1}
```

By-method and choice/Zorn proof bodies reuse `run_proof_body_stmts` from
claim/witness execution. Every statement uses the usual transaction and strict
gate. Local declarations and helper facts stay inside the proof; any failed
step fails the enclosing statement. Extension and choice/Zorn parsers now open
a local parse scope as well. Strategy bodies retain their fact-only contract.

```litex
# Previously accepted; now rejected at source WD before computation.
# algo identity(x N) N by cases:
#     case x = x: x
# eval identity(-1)
algo identity(x N) N by cases:
    case x = x: x
eval identity(0)
```

Eval success carries source-object WD evidence before rewrite/evaluation. Its
WD failure is visible in Normal and Detailed JSON with the offending object
and failed domain stage. Evaluation output is not asserted as a proof fact.

## Acceptance artifacts and evidence

- [Finite-set and nested-proof tracer](../../../stmt_nodes/by/finite_set_conditional_proof_steps.lit).
- [Eval domain tracer](../../../stmt_nodes/command/eval_source_domain.lit).
- [Template strict tracer](../../../stmt_nodes/unsafe/template_strict_policy.lit).
- [Before/after, CLI commands, and gate journal](../../proof_journals/statement_boundary_repairs.json).
- [Executable Rust boundaries](../../../../tests/unit/execute/statement_boundaries/tests.rs).

Direct CLI successes require exit 0, top-level `success: true`, and no
`session_error`; strict rejection requires the specific forbidden-trust error.
The source-owned statement manifest preserves the unchanged old reproductions
as ordinary boundaries and adds false-conditional and invalid-eval controls.
The current CLI lacks `-runner`/`-before`/`-compact` and literal `try:`; this
policy/tooling drift is recorded rather than misreported as successful gates.

Verified checkpoints:

- Seven focused boundary/JSON/tracer Rust tests pass.
- 137 transaction/rollback tests and ten eval tests pass.
- The registered examples filter passes its two tracer tests, including all
  three new `.lit` artifacts; this is not a whole examples-tree scan.
- Statement-fixture integration passes.
- 117 runnable fences in touched documentation, including the updated audit,
  pass. Historical cart and invalid-eval audit probes are explicitly marked as
  negative/illustrative; their actual rejection controls remain executable.
- The initial complete CLI suite passed 371/371 with four unrelated gaps.
  The final replay passes all task-owned outcomes but reports one unrelated
  stale K002 expectation: concurrent template-fact work now accepts
  `\member<R> $in R`, while its gap still expects rejection. The exact final
  report is retained in the journal; this task did not change K002 semantics
  or its expectation. The other three recorded gaps remain as before.

No successful gate here establishes arbitrary theorem soundness or adds
Cartesian-domain enumeration or compiler support.
