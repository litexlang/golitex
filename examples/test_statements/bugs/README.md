# Statement issue index

## Task context

- Task: per-statement regression suite requested on 2026-10-01; issue organization requested on 2026-10-02.
- Scope: all statement-suite problem records.
- Related workspace: golitex.

Ten reproductions remain open across eight execution/verifier issue groups. K001 is now a checked success regression. The user reclassified K003 as a current proof-search limitation; its accepted explicit equality chain is ordinary regression coverage. Each execution-issue `<statement>/<issue>/` directory contains `repro.lit`, `README.md`, and `observed.json`. Stable K-numbers identify issue groups; K007 and K009 each have two statement variants. There is also one displayed-statement defect (D001), using an existing registered source fixture. Open means the desired behavior remains unmet, not that a proposed diagnosis is proven. This inventory covers the problems found by the statement-suite task; it does not claim that all language bugs have been discovered.

## Open issue groups

| Issue | Problem | Statement folders | Status |
| --- | --- | --- | --- |
| K002 | Template member loses its usable carrier fact | [DefTemplateStmt](def_template_stmt/K002-template-member-carrier/README.md) | open |
| K004 | Recursive call under addition does not reduce to its value | [HaveFnByInducStmt](have_fn_by_induc_stmt/K004-recursive-call-under-addition/README.md) | open |
| K005 | Negated existence is not derived from the checked universal exclusion | [Fact](fact/K005-finite-negated-existence/README.md) | open |
| K006 | Strict mode accepts trust-have inside a template | [DefTemplateStmt](def_template_stmt/K006-strict-template-trust-have/README.md) | open |
| K007 | Enumeration proof bodies cannot use their quantified binder | [ByForStmt (K007-for)](by_for_stmt/K007-for-binder-proof-body/README.md), [ByEnumerateFiniteSetStmt (K007-enumerate)](by_enumerate_finite_set_stmt/K007-enumeration-binder-proof-body/README.md) | open |
| K008 | Advertised finite Cartesian-product enumeration is unsupported | [ByForStmt](by_for_stmt/K008-finite-cartesian-domain/README.md) | open |
| K009 | Enumeration does not discharge conditional targets using their premises | [ByForStmt (K009-for)](by_for_stmt/K009-conditional-for-goal/README.md), [ByEnumerateFiniteSetStmt (K009-enumerate)](by_enumerate_finite_set_stmt/K009-conditional-enumeration-goal/README.md) | open |
| K010 | Arithmetic target over a displayed finite numeric carrier fails enumeration | [ByEnumerateFiniteSetStmt](by_enumerate_finite_set_stmt/K010-enumeration-arithmetic-carrier/README.md) | open |

## Resolved issue groups

| Issue | Result | Record |
| --- | --- | --- |
| K001 | Callable aliases reduce directly using stored function equality evidence | [Acceptance and solution](../experience/problem_notes/K001-callable-alias-direct.md) |

## Reclassified capability limitations

K003 requires an explicit recursive equality chain and is no longer an open bug. See its [accepted source and decision](../experience/problem_notes/K003-explicit-recursive-equation-chain.md).

## Additional output issue

| Issue | Problem | Statement folder | Status |
| --- | --- | --- | --- |
| D001 | Missing space in printed trust-have | [TrustHaveStmt](trust_have_stmt/D001-missing-display-space/README.md) | open |

D001's original source executes successfully; its printed statement loses a separator. The current runner checks execution, so this output defect needs its separate acceptance check before closure. It is not counted among the ten remaining manifest gap reproductions.

## Related statement folders

- [DefAlgoByInducStmt](def_algo_by_induc_stmt/README.md) (cross-reference; no additional confirmed bug)
- [TrustHaveStmt](trust_have_stmt/README.md) (cross-reference; no additional confirmed bug)
- [HaveObjInNonemptySetStmt](have_obj_in_nonempty_set_stmt/README.md) (cross-reference; no additional confirmed bug)

## Restrictions and tooling observations

These are separate from the open bug count. Existing rejection controls stay in `negative/` and `boundaries/`; the matching statement folder explains the limitation and links its evidence.

- [AxiomStmt](axiom_stmt/limitations.md)
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
4. Run the complete suite. The gap-free gate must continue failing until all recorded gaps are resolved.

```bash
python3 examples/test_statements/run.py
python3 examples/test_statements/run.py --require-no-gaps
```

The ordinary runner checks current observations and prints every known issue. A green ordinary run does not mean these bugs are fixed. A behavior change intentionally creates an expectation mismatch until the corresponding issue/manifest is reviewed.

Evidence: [current full verification](../proof_journals/bug_organization_verification.json). Earlier authoring and acceptance captures keep their historical paths; [organization receipt](../proof_journals/bug_organization.json) maps old paths to current folders.
