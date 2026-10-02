# Builtin entry verification — 2026-10-02

`VerifyState::can_use_builtin_rule` replaces the builtin round with one boolean
entry permission. `remaining_deep_search_depth` independently starts at 3;
`StrategySearch::DEPTH_LIMIT` remains 16. `after_deep_search` preserves builtin
permission. All constructors and forwarded states carry both fields.

Builtin requirements go through `verify_builtin_rule_premise`. Their truth
search disables ordinary builtin entry, deep search and rewrite. Existing
known/citation and calculation leaves remain available. A stored or literal
function body can supply one checked substitution, with an existing function
path and a checked residual equality; a second body unfold is rejected.
Atomic premise WD keeps caller permissions and equality-peer restrictions,
without storing WD. No mathematical rule, AST field, owned runtime/environment
state, storage transaction, or equality-peer expansion policy was changed.

The runnable acceptance file is
[`builtin_entry_boolean.lit`](../../../examples/proof_nodes/atomic/by_builtin_rule/builtin_entry_boolean.lit).
Its source-order native persistent session and clean strict run both succeed.
The source-owned [journal](../../../examples/proof_nodes/proof_journals/builtin_entry_boolean.json)
records the accepted blocks, negative boundaries, CLI compatibility drift and
before/after evidence.

## Visible compatibility boundary

The Manual function-range example formerly proved
`fn_range(shift) $in power_set(Z)` by continuing into subset-definition search
inside the builtin premise. With that route disabled it first states
`fn_range(shift) $subset Z`. The same theorem still verifies separately; the
power-set rule then cites it. The original snippet and its precise changed
outcome are preserved in the journal rather than counted as unchanged source.

## Verification

- `cargo build --release`: pass.
- `cargo test --release --no-fail-fast`: 462 library tests pass; two existing
  tests fail. The statement integration test passes; binary/doc targets have
  no tests. All seven new builtin policy regressions pass.
- The original full pre-edit baseline was 450 pass / one surjection-cardinality
  failure. The additional signature-citation assertion fails intermittently;
  it was reproduced in the pre-edit source reconstructed from Git plus the
  saved initial user diff. Neither issue was changed for this task.
- Same-source comparison of 1,526 eligible examples/docs cases: no new failures
  after the documented Manual adjustment. This includes expected rejections
  and existing known gaps; 1,011 cases succeed and 515 do not. It is a comparison
  gate, not a claim that every repository example is positive or green.
- Active source, tests and maintained docs contain no old builtin-round field,
  constant or decrement helper. `git diff --check` passes.

The two pre-existing failures are
`order_stage_a_finite_set_size_union_and_surjection` and
`bounded_codomain_fallback_retains_its_selected_signature_citation`.
Raw release logs, initial source snapshots and comparison output remain in
`tmp/2026-10-02/builtin-bool-migration/` for review. The disposable reconstructed
checkout and its build cache were removed. Existing concurrent workspace edits
were retained.
