# Broader gate observations

Task: full checks during classified contra work, 2026-10-03.
Scope: proof projection expectations and Markdown audit collection.

## add2 detailed-node assertion

The existing `full_add2_chain_and_projection_boundaries` test verifies
`examples/proof_nodes/equal/by_builtin_strategy/add2_calculation_chain.lit`,
then requires `TupleComponentAtIndex` in Detailed output. Native execution
of the same file succeeds before and after. Current Detailed output has
`TupleProjection` and `Calculation`; the requested node is absent.

Category 2 candidate: inspect the intended evidence contract before changing
the projection or assertion. Earlier Detailed-node presence has not been
established; do not call mathematical verification a failure or remove the
assertion merely to obtain a green test.

[Exact current detailed tree and baseline native results](../../proof_journals/by_contra_full_kernel_failures_2026-10-02.json).

## Audit fences treated as independent positive programs

The full Markdown runner executed 408 fences and rejected 131, all in
`docs/audits/example-local-repairs-2026-10-02.md` and
`docs/audits/examples-migration-rescan-2026-10-02.md`. These reports include
retained failures and fragments with missing surrounding declarations.
Every failing source and before/after result is captured in
[the audit comparison](../../proof_journals/by_contra_docs_audit_comparison_2026-10-02.json).
130 fail in both binaries. The remaining squared-i source is nondeterministic
in baseline and after builds, as recorded in the ByContraStmt folder.

Category 1 candidate for explanatory failed/fragment fences: make runnable
context and expected outcome explicit. A broader harness expectation schema
would require discussion. Do not mark all 131 as new language bugs, skip them
en masse, or rewrite another active audit merely to make the runner green.
