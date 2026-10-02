# K005: Negated existence is not derived from the checked universal exclusion

Status: open. Primary blocker: `kernel_problem`.

## Task context

- Task: per-statement regression suite requested on 2026-10-01; issue organization requested on 2026-10-02.
- Scope: Fact / K005.
- Related workspace: golitex.

## Reproduction and captured result

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
- Desired after repair: exit 0, JSON `success: true`. Keep the same assertion and avoid introducing trust.
- Actual CLI result, process status, and original command: [observed.json](observed.json).

## Evidence and next action

The recorded behavior is reproduced. Source links below are investigation entry points, not proof that a particular function contains the defect.

- Observed: `forall x {0}: x != 1` passes; `not exist x {0} st {x = 1}` rejects with `search_proof`.
- Expected / checked control: The universal exclusion entails the negative existential. The Fact fixture covers known/local-premise negative existentials; it does not solve this search gap. An attempted `by contra` route also failed because that method currently supports atomic targets only.
- Follow-up: Add or expose the justified forall-to-not-exist route. Keep false negative-exist assertions rejected and avoid trusting the conclusion.
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

The ordinary runner checks the recorded current behavior. When this reproduction changes, it must report a mismatch until its expectation is reviewed. To close the issue, run this same source to the desired outcome, preserve the nearest rejection controls, promote the repaired case into ordinary regression coverage, update [manifest.json](../../../manifest.json), and move the resolved note to the suite's experience records. For shared IDs, check every linked statement variant before closing the group.

Back to [issue index](../../README.md).
