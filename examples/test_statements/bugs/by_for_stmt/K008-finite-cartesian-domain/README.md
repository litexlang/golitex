# K008: Advertised finite Cartesian-product enumeration is unsupported

Status: open. Primary blocker: `kernel_problem`.

## Task context

- Task: per-statement regression suite requested on 2026-10-01; issue organization requested on 2026-10-02.
- Scope: ByForStmt / K008.
- Related workspace: golitex.

## Reproduction and captured result

[repro.lit](repro.lit) contains the unchanged source from `known_gaps/finite-cartesian-domain.lit`. Run from the repository root:

```bash
target/release/litex -lang en -strict -f examples/test_statements/bugs/by_for_stmt/K008-finite-cartesian-domain/repro.lit
```

```litex
# Known gap: K008
# Desired success: true
# See todo.md; runner checks observed behavior explicitly.

by for:
    ? forall p cart({1, 2}, {3, 4}):
        p = p
```

- Current: exit 1, JSON `success: false`.
- Desired after repair: exit 0, JSON `success: true`. Keep the same assertion and avoid introducing trust.
- Actual CLI result, process status, and original command: [observed.json](observed.json).

## Evidence and next action

The recorded behavior is reproduced. Source links below are investigation entry points, not proof that a particular function contains the defect.

- Observed: The reflexive universal over `cart({1, 2}, {3, 4})` parses but rejects with `by_for`.
- Expected / checked control: The Manual describes supported finite Cartesian products. `resolve_param_domain_values` currently accepts only displayed list sets, ranges, and closed ranges; its general Obj arm rejects this Cartesian carrier.
- Follow-up: Align the documented Cartesian enumeration interface with implementation. Check the four tuples, empty-factor vacuity, and product dimensionality without broadening to arbitrary infinite products.
- Primary blocker: `kernel_problem`.

Source entry points:

- [src/execute/execute_by_stmt/enumerate_forall.rs](../../../../../src/execute/execute_by_stmt/enumerate_forall.rs)

## Controls and acceptance

- Primary positive controls: [by_for_stmt.lit](../../../by_for_stmt.lit).
- Rejection controls:
  - [false-range-instance.lit](../../../negative/by_for_stmt/false-range-instance.lit)
  - [unbounded-carrier.lit](../../../negative/by_for_stmt/unbounded-carrier.lit)
  - [false-proof-body.lit](../../../negative/by_for_stmt/false-proof-body.lit)

```bash
python3 examples/test_statements/run.py --leaf ByForStmt
```

The ordinary runner checks the recorded current behavior. When this reproduction changes, it must report a mismatch until its expectation is reviewed. To close the issue, run this same source to the desired outcome, preserve the nearest rejection controls, promote the repaired case into ordinary regression coverage, update [manifest.json](../../../manifest.json), and move the resolved note to the suite's experience records. For shared IDs, check every linked statement variant before closing the group.

Back to [issue index](../../README.md).
