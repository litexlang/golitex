# Uncatalogued Builtin Mechanism Families

Generated deterministically from the current source inventory. The
classification is a migration queue, not a proof that similarly named
rules have interchangeable semantics.

## `mathematical_leaf_law`

- Rows: **127**; direct producers: **120**; exact compiler consumers: **1**.
- Representative: `builtin.verify.atomic.function_membership.verify_value_in_definition_return_set` (`UncataloguedBuiltinRule::VerifyValueInDefinitionReturnSet`).
- Representative producer: `src/verification/atomic/function_membership.rs:74`.
- Result migration: Promote the producer to a typed certificate that fixes the exact target and required premises.
- Lean migration: Call one named proved Lean theorem adapter after certificate validation; keep one explicit route per stable ID.
- Classification basis: default leaf candidate pending exact target/premise review.

## `checked_computation_or_reflection`

- Rows: **22**; direct producers: **22**; exact compiler consumers: **0**.
- Representative: `builtin.verify.equality.core.verify_equal_fact_by_direct_evaluation` (`UncataloguedBuiltinRule::VerifyEqualFactByDirectEvaluation`).
- Representative producer: `src/verification/equality/core.rs:356`.
- Result migration: Retain the checked input, normalized output, and reflection witness instead of a display result.
- Lean migration: Use a fixed kernel-checked reflection theorem; never ask a target tactic to rediscover the computation.
- Classification basis: producer is evaluation/reflection-shaped.

## `proof_composition_or_recursive_strategy`

- Rows: **28**; direct producers: **28**; exact compiler consumers: **0**.
- Representative: `builtin.execute.explicit_verify.theorem_application.exec_builtin_thm_stmt_impl` (`UncataloguedBuiltinRule::ExecBuiltinThmStmtImpl`).
- Representative producer: `src/execution/proof_directives/theorem_application.rs:850`.
- Result migration: Retain ordered child Results and the composition constructor selected by the verifier.
- Lean migration: Compile children first and assemble their proofs with one structural Lean combinator.
- Classification basis: identity names an intermediate Result/composition boundary.

## `dispatcher_or_search_helper`

- Rows: **86**; direct producers: **83**; exact compiler consumers: **1**.
- Representative: `builtin.verify.equality.function.verify_fn_equal_fact_with_builtin_rules.01` (`UncataloguedBuiltinRule::VerifyFnEqualFactWithBuiltinRules01`).
- Representative producer: `src/verification/equality/function.rs:118`.
- Result migration: Return the selected terminal certificate/child Result; retire a helper identity that proves no proposition.
- Lean migration: Do not create a theorem for search control flow; compile only the selected semantic certificate.
- Classification basis: producer is an explicit builtin strategy/dispatcher boundary.

## `duplicate_or_orientation_candidate`

- Rows: **128**; direct producers: **121**; exact compiler consumers: **0**.
- Representative: `builtin.verify.equality.core.verify_equal_fact_by_builtin_rules_and_known_equalities.01` (`UncataloguedBuiltinRule::VerifyEqualFactByBuiltinRulesAndKnownEqualities01`).
- Representative producer: `src/verification/equality/core.rs:1145`.
- Result migration: Compare exact targets, premise order, orientation, and retained evidence before merging schemas.
- Lean migration: Share a proved theorem only after validation, while preserving an explicit route for every stable rule ID.
- Classification basis: numbered sibling identities require schema comparison before separate theorems.

## `evidence_contract_gap`

- Rows: **23**; direct producers: **23**; exact compiler consumers: **0**.
- Representative: `builtin.verify.atomic.definition.verify_choice_function_for_fact_by_definition` (`UncataloguedBuiltinRule::VerifyChoiceFunctionForFactByDefinition`).
- Representative producer: `src/verification/atomic/definition.rs:163`.
- Result migration: Extend the verifier Result with the missing target, binding, FactId, scope, or ordered child evidence.
- Lean migration: Keep fail-closed until the richer evidence can select one deterministic proof adapter.
- Classification basis: definition/quantifier replay needs richer structured evidence than one identity.

## `target_abi_decision`

- Rows: **8**; direct producers: **8**; exact compiler consumers: **0**.
- Representative: `builtin.verify.atomic.function_membership.verify_indexed_value_in_definition_return_set_via_cart_projection` (`UncataloguedBuiltinRule::VerifyIndexedValueInDefinitionReturnSetViaCartProjection`).
- Representative producer: `src/verification/atomic/function_membership.rs:165`.
- Result migration: Freeze the exact native carrier/wrapper and required eliminators before changing the certificate.
- Lean migration: Block emission until the user-owned semantic decision has a proved Core/Rules contract.
- Classification basis: producer targets a constructor family with an explicit object/fact compiler gap.

## Review boundary

The user reviews carrier semantics, theorem sharing, and whether the
representative law matches the intended mathematics. Codex owns exact
producer tracing, certificate migration, explicit dispatch, and gates.
