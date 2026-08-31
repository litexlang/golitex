# Direct Compiler Integration Baseline

Recorded: 2026-08-31 08:57 CST  
Classification: `B-H3-01 baseline_external`

## Broad gate

```sh
cargo test --release --test stmt_result_to_lean_compiler_tracers
```

- Exit: `101`
- Result: 55 passed, 21 failed, 0 ignored, 76 total.
- Duration after the current release build: 5.18s test execution.
- Boundary: these are generated-source expectation drifts in the shared dirty
  compiler baseline. They are not evidence that the generated modules fail the
  Lean kernel, and Day 1 does not overwrite their expected strings.

Exact failing tests:

1. `builtin_strategy_result_marks_each_selected_layer_and_replays_exact_rules`
2. `collections_and_aggregates_use_exact_typed_carriers`
3. `compound_anonymous_functions_replay_their_owned_wd_scope`
4. `conjunction_disjunction_and_alpha_forall_citations_replay_exact_evidence`
5. `conjunction_projection_replays_inferred_fact_ids`
6. `existential_intro_and_elim_use_native_carrier_and_exact_projections`
7. `known_equality_paths_replay_same_symmetry_and_transitivity`
8. `known_forall_multi_conclusion_fact_id_provenance_compiles_both_exact_projections`
9. `litex_to_mathlib_pipeline_showcase_generated_lean_has_not_drifted`
10. `multilayer_application_preserves_each_unary_source_contract`
11. `named_real_functions_compile_compound_bodies_and_domain_clauses`
12. `nested_forall_premises_replay_parameter_aliases_and_normalization`
13. `not_equal_symmetry_negates_heterogeneous_same`
14. `order_tracer_compiles_catalog_rule_and_rejects_non_catalog_transitivity`
15. `predicate_backed_witness_compiles_all_retained_fact_ids`
16. `proof_scope_tracer_emits_named_theorem_claim_and_example`
17. `rational_and_natural_carrier_closures_replay_exact_rules`
18. `real_sequence_definitions_stable_tracer_generated_lean_has_not_drifted`
19. `set_extension_combines_two_typed_subset_reflexivity_child_results`
20. `set_extension_compiles_nested_finite_enumeration_proof_steps`
21. `subtractive_strategy_rule_compiles_from_registered_certificate`

## First focused failure

```sh
cargo test --release --test stmt_result_to_lean_compiler_tracers \
  conjunction_projection_replays_inferred_fact_ids -- --exact --nocapture
```

- Exit: `101`
- Location: `tests/integration/stmt_result_to_lean_compiler_tracers.rs:1217`
- First assertion:

```text
generated.contains("have __infer0_0 : ¬ Litex.Same a b := (__domain1).1")
```

The current compiler changed the generated proof/name shape. Resolve this as a
single regeneration/expectation ownership pass after active compiler edits
stabilize; do not hand-edit generated Lean or repeatedly rerun the red suite.

## Dependency-changed rerun and failure families

Recorded: 2026-08-31 09:09 CST

Shared compiler implementation changed after the 08:57 baseline, so one broad
rerun was permitted. It again exited `101` with 55 passed and 21 failed after
waiting for the shared Cargo build lock and rebuilding for 1m10s. Each failing
test was then run directly from the built test binary to capture its first
boundary without another Cargo build.

`integration_failure_families.tsv` accounts for all 21 failures exactly:

- 13 `kernel_checked_expectation_drift`: Rust compilation succeeds and a
  focused generated module passes real Lean, but the test pins obsolete local
  names, carrier syntax, certificate spelling, or a former negative boundary;
- 2 `kernel_checked_checked_in_drift`: the regenerated showcase and Example 64
  modules both pass real Lean but differ from their checked-in generated files;
- 6 `compiler_gap`: five fail closed in Rust before Lean and the nested-forall
  probe emits a module that real Lean rejects at its `fnApply` membership
  argument.

The focused probes live only in
`tmp/2026-08-30/one-week-tolean-day1/`. No integration assertion, checked-in
generated module, or active compiler path was rewritten during this audit.

## Hash-bound H3 replay

Recorded: 2026-08-31 09:59–10:03 CST

The newest release test executable listed all 76 tests and, while both its
SHA-256 and the Rust-source fingerprint stayed fixed, reproduced the exact
same result in 5.38s: exit `101`, 55 passed, 21 failed. Its failure-name set is
identical to `integration_failure_families.tsv`.

`cargo test --release --test stmt_result_to_lean_compiler_tracers --no-run`
then completed once at the same Rust fingerprint and named that same binary,
proving a source-to-binary binding for the recorded historical snapshot. The
full structured record is `integration_gate_evidence.json`.

Immediately afterward the active RunOptions/pipeline/API refactor changed the
Rust fingerprint, so the evidence is correctly `current_valid:false`. One
dependency-changed rebind was attempted and exited `101` with 15 compiler
errors while its own source fingerprint changed. The first error was
`src/pipeline/run.rs:22:41`: `ExecutionOption` was not imported. This is
`B-H3-02 baseline_external`; Codex did not edit the active runtime, pipeline,
or CLI paths and will not retry until that refactor reaches a new coherent
state.

`run_integration_gate.py` now automates that binding and refuses to overwrite
the prior report on Cargo failure, fingerprint drift, binary drift, total
drift, or failure-ledger drift. Its first real run reached a new compiled test
binary but exited `1` because Rust source changed during the Cargo phase; the
mtime of `integration_gate_evidence.json` remained 10:03:47, proving the
failed attempt did not replace the historical evidence.

## Current 56/20 transition

Recorded: 2026-08-31 10:37–10:38 CST

The RunOptions/pipeline refactor reached a coherent Rust snapshot:
`cargo check --all-targets` passed at unchanged fingerprint `e7479016...`.
The hash-bound integration runner then built and executed the release test
binary. It deliberately rejected the old ledger because the result improved
from 55/21 to 56/20: there were no new failures, and
`litex_to_mathlib_pipeline_showcase_generated_lean_has_not_drifted` is now a
pass. The maintained ledger and 76-row inventory were updated by removing only
that resolved row.

The current 20 failures classify as 13 kernel-checked expectation drifts, one
checked-in Example 64 drift, and six genuine compiler gaps. A second gate run
must reproduce exactly this set under one unchanged source/binary fingerprint
before `integration_gate_evidence.json` becomes current again.

That exact second run succeeded at 10:44 CST: Cargo bound the test binary to
Rust fingerprint `4eb404d6...`, and the unchanged binary reported 56 pass / 20
classified failures / 76 total. `integration_gate_evidence.json` was current
for that snapshot. At 10:47 the active CLI/runtime refactor changed Rust again,
so the report is now deliberately marked historical; the 56/20 transition is
still reproducible evidence, not a claim about the later incomplete refactor.
