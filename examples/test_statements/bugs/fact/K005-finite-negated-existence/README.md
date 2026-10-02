# K005: Explicit by-contra cannot yet target negative existence

Status: open. Primary blocker: `kernel_problem`. Repair ownership: category 2 candidate, locality provisional pending diagnosis; Codex owns the investigation.

## Task context

- Task: per-statement regression suite requested on 2026-10-01; issue organization requested on 2026-10-02.
- Scope: Fact / K005.
- Related workspace: golitex.

## Original automatic-search observation

[repro.lit](repro.lit) contains the unchanged source from `known_gaps/finite-negated-existence.lit`. Run from the repository root:

```bash
target/release/litex -lang en -strict -f examples/test_statements/bugs/fact/K005-finite-negated-existence/repro.lit
```

```litex
# Known gap: K005
# Desired success: true
# See todo.md; runner checks observed behavior explicitly.

forall x {0}:
    x != 1
not exist x {0} st {x = 1}
```

- Current: exit 1, JSON `success: false`.
- This bare shortcut is not a required automatic conversion after the maintainer's clarification below. Keep the same mathematical conclusion in an explicit proof; avoid trust. The manifest and original observed.json still retain this historical bare-input observation until the preferred explicit reproduction is promoted during repair.
- Actual CLI result, process status, and original command: [observed.json](observed.json).

## Requested finite-enumeration route (2026-10-02)

Task: the user requests `by enumerate finite_set` for this proof.

```litex
by enumerate finite_set:
    ? forall x {0}:
        x != 1
not exist x {0} st {x = 1}
```

The enumeration succeeds and stores the universal exclusion. The original negative-existence conclusion still rejects with `search_proof`. Directly putting `? not exist x {0} st {x = 1}` under the enumeration header rejects at parse time: `goal must be a single forall fact`. An explicit contradiction route also reaches the currently unsupported compound-goal negation boundary.

All three concrete sources and current release outputs are in [k005_enumeration_attempts.json](../../../proof_journals/k005_enumeration_attempts.json).

The maintainer's repair delegation (2026-10-02) removes the generic pending permission round for a justified local repair. A successful universal statement alone is not proof of the original negative-existence statement. The newer direction is to use an explicit by-contra proof, not require a dedicated automatic conversion rule.

The [current recheck](../../../proof_journals/stmt_repair_plan_classification_2026-10-02.json) still reports exit 1 and statement results `[true, false]` for both the unchanged input and the requested enumeration form. This round updated classification and evidence only; it did not implement the repair.

## Maintainer's explicit-proof direction (2026-10-02)

Missing automatic `forall not` → `not exist` conversion alone is not a bug to repair when a checked explicit proof suffices. The mathematically justified preferred route is:

```litex
by enumerate finite_set:
    ? forall x {0}:
        x != 1
by contra:
    ? not exist x {0} st {x = 1}
    obtain a from exist x {0} st {x = 1}
    a != 1
    impossible a = 1
not exist x {0} st {x = 1}
```

This source was tested and **does not yet pass**: enumeration succeeds, contra fails before its proof body, and the final citation fails. `negate_fact_for_contra` only accepts atomic goals; this target is NotExist. The [clarification journal](../../../proof_journals/k005_contra_preference_2026-10-02.json) retains source, binary hash and results, plus passing atomic-contra and not-forall counterexample controls. No production Rust was changed.

The remaining issue is that explicit command boundary, not a requirement for automatic quantifier-duality search. Current not-forall verification constructs and verifies a counterexample existential; that alone does not establish general forward inference from an assumed not-forall.

## Evidence and next action

The recorded behavior is reproduced. Source links below are investigation entry points, not proof that a particular function contains the defect.

- Observed: `forall x {0}: x != 1` passes; `not exist x {0} st {x = 1}` rejects with `search_proof`.
- Expected / checked control: The universal exclusion entails the negative existential. The Fact fixture covers known/local-premise negative existentials; it does not solve this search gap. An attempted `by contra` route also failed because that method currently supports atomic targets only.
- Owner / next action: Codex traces `negate_fact_for_contra`, the existing NotExist/Exist payloads, and assumption→obtain→closing evidence. Investigate a bounded NotExist target branch before changing global search or enabling all compound targets. No dedicated automatic quantifier conversion is planned.
- Invariant / acceptance: the explicit proof above and final negative-existence citation pass; false goals, wrong carriers/missing premises and leaked witness assumptions reject; existing atomic-contra and Fact coverage stay valid. Preserve genuine proof evidence. The original bare shortcut may remain a limitation and need not start passing.
- Escalation: discuss before changing global search, forall storage/projection, shared representation, AST fields, or environment lifecycle. Investigation and an established local repair use the standing category-2 delegation; unknown scope is not a reason to ask the maintainer to diagnose it.
- Primary blocker: `kernel_problem`.

Source entry points:

- [src/execute/execute_fact_stmt](../../../../../src/execute/execute_fact_stmt)

## Controls and acceptance

- Primary positive controls: [fact.lit](../../../fact.lit).
- Rejection controls:
  - [false-equality.lit](../../../negative/fact/false-equality.lit)
  - [false-membership.lit](../../../negative/fact/false-membership.lit)
  - [false-forall.lit](../../../negative/fact/false-forall.lit)
  - [undefined-object.lit](../../../negative/fact/undefined-object.lit)

```bash
python3 examples/test_statements/run.py --leaf Fact
```

The ordinary runner currently checks the historical bare-input observation; it does not gate the preferred explicit proof, which is captured in the clarification journal. Before closing K005, promote that explicit proof into normal regression coverage, retain the bare shortcut as a documented automatic-search limitation, preserve the nearest rejection controls, update [manifest.json](../../../manifest.json), and move the solution note to experience records. Do not require an automatic bare-goal rule or claim the explicit proof passes before it does.

Back to [issue index](../../README.md).
