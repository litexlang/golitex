# K002: Template definitions publish their facts

Status: resolved on 2026-10-02.

## Before and now

```litex
# Before: declaration succeeded, membership failed at search_proof (K002).
# template<S nonempty_set>:
#     have member S
# \member<R> $in R

template<S nonempty_set>:
    have member S
\member<R> $in R
forall T nonempty_set:
    \member<T> $in T
```

The unchanged [original reproduction](../../bugs/def_template_stmt/K002-template-member-carrier/repro.lit)
now passes without trust. [Historical failure](../../bugs/def_template_stmt/K002-template-member-carrier/observed.json)
and [current CLI result](../../bugs/def_template_stmt/K002-template-member-carrier/verified.json)
are preserved separately. The [persistent tracer](../../../stmt_nodes/definition/template_definition_facts.lit)
checks object, existential, obtain, replacement, formula, case, recursive, and
unique-function templates.

## Mechanism and boundaries

After the body succeeds locally, its recorded definition stores are read by
fact ID. The single body binding is substituted with `\name<template args>`;
the original template binders and premises prefix each resulting fact.
Existing function binders, domains, case guards, and uniqueness premises are
retained. `store_fact_and_infer` publishes the resulting forall in the enclosing
statement transaction. Source IDs link the publication to the retained local
body evidence. Local assumptions and unrelated proof-search facts are not
published. Neither AST shapes nor Env/Runtime state ownership changed.

Known-forall matching now descends into the arguments of template occurrences
with equal canonical template identities. The original matcher did not bind a
parameter appearing there; storing the member forall alone therefore did not
make it usable. Ordinary `cite_forall` now records the proof.

Arbitrary members acquire membership, not uniqueness or a chosen scalar value.
Template domains and case guards remain required. Wrong carriers/arguments and
false branch equations reject. Failed templates and enclosing failed claims
discard publications. Trust bodies retain the existing nonstrict policy.

The current parser still rejects a comparison at the end of a template header
such as `template<a R: a > 0>:` (the closing `>` is read as another comparison).
The accepted conditional probe uses the existing predicate form:

```litex
template<S set: $is_nonempty_set(S)>:
    have selected S
\selected<R> $in R
```

Recursive arithmetic retains the existing explicit equality-chain requirement;
the tracer uses the displayed predecessor argument `1 - 1`. This change does
not expand the proof-search budget or repair those separate parser/search limits.

## Acceptance

```bash
cargo test --release --lib execute::execute_def_template_stmt::tests -- --nocapture
cargo test --release --lib declaration_binding_tests -- --nocapture
cargo test --release --lib known_search_tests -- --nocapture
cargo test --release --lib exec_stmt_transaction_tests -- --nocapture
cargo test --release --lib induction_repair_tests -- --nocapture
cargo test --release --lib json_output -- --nocapture
target/release/litex -lang en -strict -f examples/stmt_nodes/definition/template_definition_facts.lit
python3 examples/test_statements/run.py --leaf DefTemplateStmt
```

The ten dedicated [Rust tests](../../../../tests/unit/execute/template_definition_facts/tests.rs)
cover all eleven body variants, dependent parameters, original domain facts,
rejection and rollback, live Eval/root/imported identities, and Normal/Detailed
JSON. Release successes require exit 0, top-level `success: true`, and no
`session_error`. Current results are recorded in the
[journal](../../proof_journals/template_definition_facts.json).

Verified checkpoint: ten focused tests and 226 related binding/search,
transaction, induction, and JSON tests pass. The registered `run_examples`
filter runs three tracer tests, including this feature's full strict source.
All 122 executable fences in the touched documentation and solution records
pass. The complete statement suite runs 371 checks over 50 leaves without
unexpected failures; K004, K005, and K010 remain recorded gaps. The statement
fixture integration test also passes.

The additional direct template scan passes 12 of 13 artifacts. Its remaining
`let_template_struct_aliases.lit` failure was already listed in the
[baseline equality audit](../../../../src/execute/execute_fact_stmt/verify_atomic_fact/verify_equality/verification.md#remaining-baseline-failures).
Two declaration-binding module checks pass. The unchanged
`trusted_template_prefix/litex.config` still uses the obsolete `[hierarchy]`
section and fails at launch before execution; its diagnostic and source are
preserved in the journal. Those separate artifacts were not rewritten.
