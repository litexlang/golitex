# K010: Arithmetic target over a displayed finite numeric carrier fails enumeration

Status: open. Primary blocker: `kernel_problem`.

## Task context

- Task: per-statement regression suite requested on 2026-10-01; issue organization requested on 2026-10-02.
- Scope: ByEnumerateFiniteSetStmt / K010.
- Related workspace: golitex.

## Reproduction and captured result

[repro.lit](repro.lit) contains the unchanged source from `known_gaps/enumeration-arithmetic-carrier.lit`. Run from the repository root:

```bash
target/release/litex -lang en -strict -f examples/test_statements/bugs/by_enumerate_finite_set_stmt/K010-enumeration-arithmetic-carrier/repro.lit
```

```litex
# Known gap: K010
# Desired success: true
# See todo.md; runner checks observed behavior explicitly.

by enumerate finite_set:
    ? forall n {0, 1}:
        n + 0 = n
```

- Current: exit 1, JSON `success: false`.
- Desired after repair: exit 0, JSON `success: true`. Keep the same assertion and avoid introducing trust.
- Actual CLI result, process status, and original command: [observed.json](observed.json).

## Evidence and next action

The outer failure is reproduced. The exact nested failure stage and proposed cause remain unconfirmed; source observations below are investigation leads.

- Observed: The bodyless universal `n + 0 = n` over `{0, 1}` rejects with `by_enumerate`; the reflexive target `n = n` over the same set passes.
- Expected / checked control: Each displayed value is a natural and the arithmetic identity holds. The shared enumerator checks goal well-definedness before generating assignments, so numeric-carrier evidence at that boundary is a candidate cause. Normal JSON does not establish the exact nested failure stage; that diagnosis remains to be confirmed.
- Follow-up: Inspect goal well-definedness and finite-carrier numeric inference before changing arithmetic rules. Compare a range domain, an explicit checked carrier bridge, and a nonnumeric finite set.
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

Back to [issue index](../../README.md).
