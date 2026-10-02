# K009-enumerate: Enumeration does not discharge conditional targets using their premises

Status: resolved on 2026-10-02. The reproduction is now an ordinary boundary regression.

Current acceptance: [statement boundary repairs](../../../experience/problem_notes/statement-boundary-repairs.md).
`observed.json` and the before-repair discussion below are historical evidence;
current expected behavior is recorded in the suite manifest.

## Task context

- Task: per-statement regression suite requested on 2026-10-01; issue organization requested on 2026-10-02.
- Scope: ByEnumerateFiniteSetStmt / K009.
- Related workspace: golitex.

## Reproduction and captured result

[repro.lit](repro.lit) contains the unchanged source from `known_gaps/conditional-enumeration-goal.lit`. Run from the repository root:

```bash
target/release/litex -lang en -strict -f examples/test_statements/bugs/by_enumerate_finite_set_stmt/K009-conditional-enumeration-goal/repro.lit
```

```litex
# Known gap: K009-enumerate
# Desired success: true
# See todo.md; runner checks observed behavior explicitly.

by enumerate finite_set:
    ? forall n {0, 1, 2}:
        n > 0
        =>:
            n != 0
```

- Current: exit 1, JSON `success: false`.
- Desired after repair: exit 0, JSON `success: true`. Keep the same assertion and avoid introducing trust.
- Actual CLI result, process status, and original command: [observed.json](observed.json).

## Evidence and next action

The outer failure is reproduced. The exact nested failure stage and proposed cause remain unconfirmed; source observations below are investigation leads.

- Observed: Both finite enumeration and bounded for reject the true conditional universal `n > 0 => n != 0` on a domain containing zero.
- Expected / checked control: The zero assignment has a false premise and imposes no conclusion obligation; positive assignments satisfy the implication. Source inspection shows conclusions are verified for every assignment without applying the forall domain facts. The Normal JSON reports only the outer phase; the exact nested failure result was not captured.
- Follow-up: Inspect conditional assignment handling in the shared enumerator. Test skipped false-premise assignments, used true-premise assumptions, and a false conclusion under a true premise.
- Primary blocker: `kernel_problem`.

Source entry points:

- [src/execute/execute_by_stmt/enumerate_forall.rs](../../../../../src/execute/execute_by_stmt/enumerate_forall.rs)

## Controls and acceptance

- Primary positive controls: [by_enumerate_finite_set_stmt.lit](../../../by_enumerate_finite_set_stmt.lit).
- Rejection controls:
  - [false-enumerated-instance.lit](../../../negative/by_enumerate_finite_set_stmt/false-enumerated-instance.lit)
  - [nonenumerable-domain.lit](../../../negative/by_enumerate_finite_set_stmt/nonenumerable-domain.lit)
  - [false-proof-body.lit](../../../negative/by_enumerate_finite_set_stmt/false-proof-body.lit)

```bash
python3 examples/test_statements/run.py --leaf ByEnumerateFiniteSetStmt
```

The ordinary runner checks the recorded current behavior. When this reproduction changes, it must report a mismatch until its expectation is reviewed. To close the issue, run this same source to the desired outcome, preserve the nearest rejection controls, promote the repaired case into ordinary regression coverage, update [manifest.json](../../../manifest.json), and move the resolved note to the suite's experience records. For shared IDs, check every linked statement variant before closing the group.

## Same issue in another statement

- [ByForStmt / K009-for](../../by_for_stmt/K009-conditional-for-goal/README.md)

Back to [issue index](../../README.md).
