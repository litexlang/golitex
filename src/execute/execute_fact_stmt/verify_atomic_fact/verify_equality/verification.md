# Equality update verification — 2026-09-30

Baseline: `af560aab3d1929b9e8bc70a76d96c5b977861025`, clean worktree before
implementation. The baseline release binary was rebuilt from that Git tree for
the same-input comparisons below. These results describe this update, not a
claim that the whole repository is green.

## Acceptance and scope

The maintained tracer is
[`peer_alpha_membership.lit`](../../../../../examples/proof_nodes/equal/by_equivalence_class/peer_alpha_membership.lit):
`let g = fn(x R) R`, `have fn f(t R) R = t`, then `f $in g`.
The baseline exits 1 and reports a proof-search failure for the membership.
The updated release exits 0 with `success: true`, no session error, and every
statement successful, under `-strict`. No trust was added.

The four identity fixtures and the named-function-shape fixture were relocated
to match the new proof routes. Their non-comment executable lines are exactly
the same as in the baseline; no mathematical target was weakened. All five and
the new tracer pass individually under `-strict`.

The update changes equality search policy, evidence, and output consumers.
It does not change AST shapes, persistent Env/Runtime state, class storage,
statement transaction ownership, or the old free-parameter storage index.
The alpha helper is moved from builtin code; identity comparison remains pure.
No Lean compiler or Lean proof gate is claimed by this verification.

## Commands and measured results

| Check | Baseline | Updated |
| --- | --- | --- |
| `cargo build --release` | passes | passes |
| Library unit suite (`cargo test --release`) | 266 pass, 11 fail | 280 pass, 8 fail |
| `cargo test --release equality_search_tests -- --nocapture` | new tests absent | 11 pass |
| `python3 tests/tooling/run_docs_markdown_files.py` on updated docs | 164/165 blocks pass | 165/165 blocks pass |
| Same 584 phase example files, run with each release binary | 563 meet expectations | 573 meet expectations |

The library suite has 11 new tests and three previously failing tests now pass:

- `execute::exec_stmt_transaction_tests::fn_set_and_set_builder_alpha_equal_builtins`
- `execute::exec_stmt_transaction_tests::membership_in_identifier_fn_set_via_trust_stored_free_params_lookup`
- `execute::exec_stmt_transaction_tests::membership_in_named_fn_set_from_known_membership_in_alpha_equal_fn_set`

No baseline-passing library test or scanned example became failing. The one
baseline docs failure is the newly added membership snippet in `docs/Manual.md`.
The Litex snippet in this directory's README was also run separately and passes.

The example scan covers `proof_nodes`, `stmt_nodes`, `wd`, `infer`, `tokenize`,
`knowledge_base`, `wd_negative`, and `equal_negative`, invoking `litex -f` with
a 30-second timeout per file. Positive files require exit 0, a successful run
envelope, no session error, and successful statements. Negative directories
require rejection; `wd_negative/identifier_undefined.lit` and
`wd_negative/obj_at_index_applied.lit` intentionally reject at parsing. The ten
additional successes include the new tracer, so they are not ten independently
established historical bug fixes. This scan does not cover module-manager or
internal examples. `def_algo_mismatch.lit` is an intentional mismatch example
outside the negative directories and remains in the nonpassing count below.

Focused tests check zero-fuel identity; free identifiers, carriers, conditions,
and binder correspondence; WD rejection of `1 / 0 = 1 / 0`; stored edge
orientation and FactIds; both peer classes; inherited builtin fuel; the ban on
another peer expansion from matching children; unchanged caller stores and
classes; strategy-entry compatibility; and Normal/Detailed JSON provenance.

## Remaining baseline failures

These eight library tests fail with both versions; `cargo test --release`
therefore still exits 101:

```text
execute::exec_stmt_transaction_tests::not_in_and_set_algebra_builtin_rules
execute::exec_stmt_transaction_tests::template_body_obtain_from_atomic_fact_wires
execute::exec_stmt_transaction_tests::template_body_obtain_from_exist_wires
execute::exec_stmt_transaction_tests::template_have_fn_by_induc_object_definition_unfold
execute::order_stage_a_remainder_tests::order_stage_a_finite_set_size_union_and_surjection
json_output::acceptance_tests::acceptance_cite_readable_no_hash_wrappers
json_output::acceptance_tests::acceptance_hot_atomic_chinese_from_known_in_n
json_output::project_normal_tests::normal_json_have_natural_then_nonnegative_by_builtin
```

These eleven scanned files do not meet the scan's expectations with either
version:

```text
examples/infer/atomic/in_index_cart.lit
examples/proof_nodes/equal/by_builtin_rule/log_arg_power.lit
examples/proof_nodes/equal/by_builtin_rule/pow_of_log_inverse.lit
examples/stmt_nodes/definition/def_algo_mismatch.lit
examples/stmt_nodes/definition/def_template_obtain_from_atomic_fact.lit
examples/stmt_nodes/definition/def_template_obtain_from_exist.lit
examples/stmt_nodes/definition/have_fn_by_induc.lit
examples/stmt_nodes/definition/let_callable_alias.lit
examples/stmt_nodes/definition/let_template_struct_aliases.lit
examples/wd/obj/index_cart.lit
examples/wd/obj/index_union.lit
```

## Policy and tooling boundaries

`StoredPathsOnly` propagates through child verifier states, including direct WD
obligations. Existing binder WD still invokes separate local store/infer
pipelines, which create their own verification states. This update does not
make the no-peer restriction global across those inference entries; see the
[architecture explanation](README.md#one-equivalence-class-stage). No candidate
count cutoff was added, so large classes can still be expensive.

Structural identity recognizes a correctly renamed dependent binder, but the
existing WD implementation rejects parameter types citing earlier binders.
The negative test preserves that boundary instead of bypassing WD.

The documented command `cargo test --release run_examples -- --nocapture`
currently matches **zero tests**. Its exit 0 is not example-coverage evidence;
the direct scan above supplies the measured coverage.

The current CLI supports `-e`, `-f`, `-session`, and `-strict`; it rejects the
policy examples' `-compact`, `-isolated`, `-runner`, and `-before` options.
Its JSON gate is `success`, not `ok`. It also rejects literal `try:` blocks.
The acceptance session therefore used ordinary source-order statements in
`-strict -e '# Equality acceptance session' -session`, with the existing
per-statement transaction boundary. The rejected command/try attempts and
successful session are recorded in the task-local JSON journal.

Raw baseline/current logs, direct tracer envelopes, the example comparison
script and JSON, and `proof_journal.json` are retained locally under
`tmp/2026-09-30/equality-same-and-peers/`. They are task evidence, not required
runtime assets. `git diff --check` passes.
