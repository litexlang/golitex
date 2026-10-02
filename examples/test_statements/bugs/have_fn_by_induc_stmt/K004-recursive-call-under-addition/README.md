# K004: Recursive call under addition does not reduce to its value

Status: open. Primary blocker: `kernel_problem`.

## Task context

- Task: per-statement regression suite requested on 2026-10-01; issue organization requested on 2026-10-02.
- Scope: HaveFnByInducStmt / K004.
- Related workspace: golitex.

## Reproduction and captured result

[repro.lit](repro.lit) contains the unchanged source from `known_gaps/recursive-call-under-addition.lit`. Run from the repository root:

```bash
target/release/litex -lang en -strict -f examples/test_statements/bugs/have_fn_by_induc_stmt/K004-recursive-call-under-addition/repro.lit
```

```litex
# Known gap: K004
# Desired success: true
# See todo.md; runner checks observed behavior explicitly.

have fn f(n N) N by induc n from 0:
    case n = 0: 0
    case n >= 1: f(n - 1) + 1
f(0) = 0
f(1 - 1) = f(0) = 0
f(1) = f(1 - 1) + 1
f(1) = 1
```

- Current: exit 1, JSON `success: false`.
- Desired after repair: exit 0, JSON `success: true`. Keep the same assertion and avoid introducing trust.
- Actual CLI result, process status, and original command: [observed.json](observed.json).

## Evidence and next action

The recorded behavior is reproduced. Source links below are investigation entry points, not proof that a particular function contains the defect.

- Observed: The definition, base equation, normalized child-call chain, and `f(1) = f(1 - 1) + 1` all pass. The final `f(1) = 1` assertion still rejects with `search_proof`.
- Expected / checked control: Substituting the checked child value 0 into the stored sum should yield 1. A direct attempt, an equality chain, and separated index/body equations were captured; no trust-free numeric closing route was found in those attempts.
- Follow-up: Inspect equality substitution under arithmetic constructors in the real recursive-definition path. Preserve the source function and decreasing measure; do not replace the recursive function with a closed formula.
- Primary blocker: `kernel_problem`.

Source entry points:

- [src/execute/execute_have_fn_by_induc_stmt.rs](../../../../../src/execute/execute_have_fn_by_induc_stmt.rs)
- [src/execute/execute_fact_stmt/verify_atomic_fact/verify_equality/by_object_definition/by_fn_application/by_have_fn_by_induc.rs](../../../../../src/execute/execute_fact_stmt/verify_atomic_fact/verify_equality/by_object_definition/by_fn_application/by_have_fn_by_induc.rs)

## Controls and acceptance

- Primary positive controls: [have_fn_by_induc_stmt.lit](../../../have_fn_by_induc_stmt.lit).
- Rejection controls:
  - [nondecreasing-recursion.lit](../../../negative/have_fn_by_induc_stmt/nondecreasing-recursion.lit)
  - [bad-base-carrier.lit](../../../negative/have_fn_by_induc_stmt/bad-base-carrier.lit)

```bash
python3 examples/test_statements/run.py --leaf HaveFnByInducStmt
```

The ordinary runner checks the recorded current behavior. When this reproduction changes, it must report a mismatch until its expectation is reviewed. To close the issue, run this same source to the desired outcome, preserve the nearest rejection controls, promote the repaired case into ordinary regression coverage, update [manifest.json](../../../manifest.json), and move the resolved note to the suite's experience records. For shared IDs, check every linked statement variant before closing the group.

Back to [issue index](../../README.md).
