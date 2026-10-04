# Statement issue index

> **统一收尾入口：** [src收尾总清单.md](../../../plan/src收尾总清单.md)（2026-10-04）。活动事项及跨来源去重在总清单维护；本页保留专项代码、决定和历史验收。新增进展应同步对应总清单ID，不能用旧快照覆盖新证据。

## Task context

- Task: per-statement regression suite requested on 2026-10-01; issue organization requested on 2026-10-02.
- Scope: all statement-suite problem records.
- Related workspace: golitex.

No K-number reproduction remains open. K005's explicit negative-existence proof now passes. K001, K002, K006, K007, K009, and K010 are checked regressions; K008 is an explicitly unsupported domain. K003 and K004 use accepted explicit equality chains as ordinary regression coverage. D001's printed statement now passes fresh-parser replay. Stable K-numbers identify issue groups; K007 and K009 each have two statement variants. Open means the desired behavior remains unmet, not that a proposed diagnosis is proven. This inventory covers the problems found by the statement-suite task; it does not claim that all language bugs have been discovered.

## Open issue groups

No K-number issue remains open. Broader requested feature work is recorded in
[ByContraStmt](by_contra_stmt/limitations.md): remaining nested classified
quantifier representation. The approved compound-closing phase has separate
[acceptance](../experience/problem_notes/by-contra-compound-closing.md); it does
not complete the nested-quantifier feature.

The maintainer delegates authoring improvements (category 1) and bounded local
Rust fixes (category 2) to Codex; nonlocal and protected AST changes require
concrete discussion. See the [suite todo](../todo.md).

## Resolved issue groups

| Issue | Result | Record |
| --- | --- | --- |
| K001 | Callable aliases reduce directly using stored function equality evidence | [Acceptance and solution](../experience/problem_notes/K001-callable-alias-direct.md) |
| K002 | Template body definition facts are stored under template binders and premises | [Acceptance and solution](../experience/problem_notes/K002-template-definition-facts.md) |
| K005 | Explicit negative-existence contradiction with checked enumeration, witness scope and final citation | [Acceptance and solution](../experience/problem_notes/K005-classified-negative-existence-contra.md) |
| K010 | Finite-set membership supplies numeric carrier evidence before enumeration | [Acceptance and solution](../experience/problem_notes/K010-finite-numeric-carrier.md) |
| D001 | Printed trust-have keeps its separator and replays successfully | [Display and replay acceptance](../experience/problem_notes/D001-trust-have-display.md) |

## Reclassified capability limitations

K003 requires an [explicit recursive equality chain](../experience/problem_notes/K003-explicit-recursive-equation-chain.md). K004 now uses the user's [explicit arithmetic chain](../experience/problem_notes/K004-explicit-recursive-increment-chain.md). Both are current automatic-search limitations and are no longer open bugs.

The [statement-boundary acceptance record](../experience/problem_notes/statement-boundary-repairs.md)
resolves K006 (strict template trust), both K007 binder-body variants, and both
K009 conditional-enumeration variants. K008 is excluded by the user and has been removed from its bug folder; its [unsupported-domain boundary and decision](../experience/problem_notes/K008-cart-excluded.md) remain as explicit rejection coverage. Other historical issue folders remain linked from the manifest boundaries.

## Rechecked internal verifier control

The formerly failing stored atomic citation under `known_only` now passes its exact Rust control (1 passed, 0 failed). Its stale open folder is removed; the [prior failure and current recheck](../experience/problem_notes/known-only-control-recheck.md) remain recorded. No causal repair attribution or complete seven-test suite acceptance is claimed.

## Additional kernel-gate observations (2026-10-03)

These are outside the original K-number statement inventory; zero manifest
K-gaps does not mean the whole kernel has no problems.

| Finding | Record | Ownership/status |
| --- | --- | --- |
| Real least-upper-bound builtin conclusion WD | [ByThmStmt](by_thm_stmt/kernel_gate_2026-10-03.md) | Category 2 candidate; missing predicate interface, before/after failure |
| Finite cardinality numeric carrier | [Fact](fact/kernel_gate_2026-10-03.md) | Category 1 vs 2 provisional; exact carrier phase recorded |
| Squared-i atomic proof nondeterminism | [ByContraStmt](by_contra_stmt/atomic_i_nondeterminism_2026-10-03.md) | Closed by accepted explicit substitution chain; historical shortcut evidence retained, no pending Rust repair |
| add2 node assertion / audit-fence collection | [Tooling](tooling/kernel_gate_2026-10-03.md) | Separate proof-output and authoring/tooling controls; no automatic assertion weakening |

## Related statement folders

- [DefAlgoByInducStmt](def_algo_by_induc_stmt/README.md) (cross-reference; no additional confirmed bug)
- [TrustHaveStmt](trust_have_stmt/README.md) (cross-reference; no additional confirmed bug)
- [HaveObjInNonemptySetStmt](have_obj_in_nonempty_set_stmt/README.md) (cross-reference; no additional confirmed bug)

## Restrictions and tooling observations

These are separate from the open bug count. Existing rejection controls stay in `negative/` and `boundaries/`; the matching statement folder explains the limitation and links its evidence.

- [AxiomStmt](axiom_stmt/limitations.md)
- [ByContraStmt](by_contra_stmt/limitations.md)
- [ByForStmt](by_for_stmt/limitations.md)
- [ByThmStmt](by_thm_stmt/limitations.md)
- [ClaimStmt](claim_stmt/limitations.md)
- [DefAbstractPropStmt](def_abstract_prop_stmt/limitations.md)
- [DefStrategyStmt](def_strategy_stmt/limitations.md)
- [DefStructStmt](def_struct_stmt/limitations.md)
- [Fact](fact/limitations.md)
- [HaveFnByInducStmt](have_fn_by_induc_stmt/limitations.md)
- [HaveObjEqualStmt](have_obj_equal_stmt/limitations.md)
- [RegisterReflexivePropStmt](register_reflexive_prop_stmt/limitations.md)
- [RegisterSymmetricPropStmt](register_symmetric_prop_stmt/limitations.md)
- [RegisterTransitivePropStmt](register_transitive_prop_stmt/limitations.md)
- [ReleaseAxiomOfChoiceStmt](release_axiom_of_choice_stmt/limitations.md)
- [ReleaseRegularityAxiomStmt](release_regularity_axiom_stmt/limitations.md)
- [SketchStmt](sketch_stmt/limitations.md)
- [TrustHaveStmt](trust_have_stmt/limitations.md)
- [TrustStmt](trust_stmt/limitations.md)
- [WitnessAtomicFact](witness_atomic_fact/limitations.md)
- [tooling](tooling/limitations.md)

## Repair workflow

1. Open one issue's README and run its exact reproduction from the repository root.
2. Compare the actual JSON and process status with its desired behavior; preserve its assertion and nearest rejection controls.
3. After a fix, promote the unchanged reproduction to ordinary regression coverage in the manifest, retain the solution in nearby experience records, and close the corresponding note/index. Check both variants of a shared issue ID.
4. Run the complete suite and its gap-free gate after record promotion. Retain the accepted explicit proof and deliberate automatic-search boundary.

```bash
python3 examples/test_statements/run.py
python3 examples/test_statements/run.py --require-no-gaps
```

The ordinary runner checks current observations and prints every known issue. A green ordinary run does not mean these bugs are fixed. A behavior change intentionally creates an expectation mismatch until the corresponding issue/manifest is reviewed.

Evidence: [organization-time full verification](../proof_journals/bug_organization_verification.json). Earlier authoring and acceptance captures keep their historical paths; [organization receipt](../proof_journals/bug_organization.json) maps old paths to current folders.

Latest K003 classification and focused acceptance: [explicit-chain capture](../proof_journals/k003_explicit_chain.json).
