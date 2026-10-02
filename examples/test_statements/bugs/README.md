# Statement issue index

## Task context

- Task: per-statement regression suite requested on 2026-10-01; issue organization requested on 2026-10-02.
- Scope: all statement-suite problem records.
- Related workspace: golitex.

One reproduction remains open: K005's negative-existence conclusion. K001, K002, K006, K007, K009, and K010 are checked regressions; K008 is an explicitly unsupported domain. K003 and K004 use accepted explicit equality chains as ordinary regression coverage. D001's printed statement now passes fresh-parser replay. Stable K-numbers identify issue groups; K007 and K009 each have two statement variants. Open means the desired behavior remains unmet, not that a proposed diagnosis is proven. This inventory covers the problems found by the statement-suite task; it does not claim that all language bugs have been discovered.

## Open issue groups

| Issue | Problem | Statement folders | Status / repair ownership |
| --- | --- | --- | --- |
| K005 | Explicit by-contra cannot target negative existence; automatic conversion is not required | [Fact](fact/K005-finite-negated-existence/README.md) | open; category 2 candidate, locality under diagnosis |

The maintainer delegates Litex authoring improvements (category 1) and justified local Rust semantic repairs (category 2) to Codex. Nonlocal changes require discussion. Current scope, next action, acceptance and escalation are in the [suite todo](../todo.md); unknown scope stays provisional until investigated.

## Resolved issue groups

| Issue | Result | Record |
| --- | --- | --- |
| K001 | Callable aliases reduce directly using stored function equality evidence | [Acceptance and solution](../experience/problem_notes/K001-callable-alias-direct.md) |
| K002 | Template body definition facts are stored under template binders and premises | [Acceptance and solution](../experience/problem_notes/K002-template-definition-facts.md) |
| K010 | Finite-set membership supplies numeric carrier evidence before enumeration | [Acceptance and solution](../experience/problem_notes/K010-finite-numeric-carrier.md) |
| D001 | Printed trust-have keeps its separator and replays successfully | [Display and replay acceptance](../experience/problem_notes/D001-trust-have-display.md) |

## Reclassified capability limitations

K003 requires an [explicit recursive equality chain](../experience/problem_notes/K003-explicit-recursive-equation-chain.md). K004 now uses the user's [explicit arithmetic chain](../experience/problem_notes/K004-explicit-recursive-increment-chain.md). Both are current automatic-search limitations and are no longer open bugs.

The [statement-boundary acceptance record](../experience/problem_notes/statement-boundary-repairs.md)
resolves K006 (strict template trust), both K007 binder-body variants, and both
K009 conditional-enumeration variants. K008 is excluded by the user and has been removed from its bug folder; its [unsupported-domain boundary and decision](../experience/problem_notes/K008-cart-excluded.md) remain as explicit rejection coverage. Other historical issue folders remain linked from the manifest boundaries.

## Rechecked internal verifier control

The formerly failing stored atomic citation under `known_only` now passes its exact Rust control (1 passed, 0 failed). Its stale open folder is removed; the [prior failure and current recheck](../experience/problem_notes/known-only-control-recheck.md) remain recorded. No causal repair attribution or complete seven-test suite acceptance is claimed.

## Related statement folders

- [DefAlgoByInducStmt](def_algo_by_induc_stmt/README.md) (cross-reference; no additional confirmed bug)
- [TrustHaveStmt](trust_have_stmt/README.md) (cross-reference; no additional confirmed bug)
- [HaveObjInNonemptySetStmt](have_obj_in_nonempty_set_stmt/README.md) (cross-reference; no additional confirmed bug)

## Restrictions and tooling observations

These are separate from the open bug count. Existing rejection controls stay in `negative/` and `boundaries/`; the matching statement folder explains the limitation and links its evidence.

- [AxiomStmt](axiom_stmt/limitations.md)
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
4. Run the complete suite. The gap-free gate continues failing while K005 remains unresolved.

```bash
python3 examples/test_statements/run.py
python3 examples/test_statements/run.py --require-no-gaps
```

The ordinary runner checks current observations and prints every known issue. A green ordinary run does not mean these bugs are fixed. A behavior change intentionally creates an expectation mismatch until the corresponding issue/manifest is reviewed.

Evidence: [organization-time full verification](../proof_journals/bug_organization_verification.json). Earlier authoring and acceptance captures keep their historical paths; [organization receipt](../proof_journals/bug_organization.json) maps old paths to current folders.

Latest K003 classification and focused acceptance: [explicit-chain capture](../proof_journals/k003_explicit_chain.json).
