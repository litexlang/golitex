# K007-enumerate: Enumeration proof bodies cannot use their quantified binder

Status: resolved on 2026-10-02. The reproduction is now an ordinary boundary regression.

Current acceptance: [statement boundary repairs](../../../experience/problem_notes/statement-boundary-repairs.md).
`observed.json` and the before-repair discussion below are historical evidence;
current expected behavior is recorded in the suite manifest.

## Task context

- Task: per-statement regression suite requested on 2026-10-01; issue organization requested on 2026-10-02.
- Scope: ByEnumerateFiniteSetStmt / K007.
- Related workspace: golitex.

## Reproduction and captured result

[repro.lit](repro.lit) contains the unchanged source from `known_gaps/enumeration-binder-proof-body.lit`. Run from the repository root:

```bash
target/release/litex -lang en -strict -f examples/test_statements/bugs/by_enumerate_finite_set_stmt/K007-enumeration-binder-proof-body/repro.lit
```

```litex
# Known gap: K007-enumerate
# Desired success: true
# See todo.md; runner checks observed behavior explicitly.

by enumerate finite_set:
    ? forall n {0, 1}:
        n = n
    n = n
```

- Current: exit 1, JSON `success: false`.
- Desired after repair: exit 0, JSON `success: true`. Keep the same assertion and avoid introducing trust.
- Actual CLI result, process status, and original command: [observed.json](observed.json).

## Evidence and next action

The outer failure is reproduced. The exact nested failure stage and proposed cause remain unconfirmed; source observations below are investigation leads.

- Observed: Both `by for` and `by enumerate finite_set` reject the binder-referencing proof body, with `by_for` / `by_enumerate` phases. Removing that body or using the constant body `1 = 1` passes.
- Expected / checked control: A proof body should refer to the current quantified assignment. The shared enumerator runs proof steps before instantiating conclusions and does not substitute the assignment into those proof steps; this source observation is a likely cause, not an independently captured nested failure result.
- Follow-up: Inspect `execute_by_stmt/enumerate_forall.rs` proof-body substitution/assignment scope. Preserve both constructs and false-proof-body rejection tests; use the controls in `by_for_stmt.lit` and `by_enumerate_finite_set_stmt.lit`.
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

- [ByForStmt / K007-for](../../by_for_stmt/K007-for-binder-proof-body/README.md)

Back to [issue index](../../README.md).
