# K001: Callable alias needs an explicit equality bridge

Status: resolved on 2026-10-02. Original blocker: `kernel_problem`.

The unchanged reproduction now succeeds directly. The original failure capture below is historical. Current design, executable negative controls, and acceptance commands are recorded in [the solution note](../../../experience/problem_notes/K001-callable-alias-direct.md). The manifest now requires success as `boundary/resolved-K001-callable-alias-direct`.

## Task context

- Task: per-statement regression suite requested on 2026-10-01; issue organization requested on 2026-10-02.
- Scope: LetObjStmt / K001.
- Related workspace: golitex.

## Reproduction and captured result

[repro.lit](repro.lit) contains the unchanged source from `known_gaps/callable-alias-direct.lit`. Run from the repository root:

```bash
target/release/litex -lang en -strict -f examples/test_statements/bugs/let_obj_stmt/K001-callable-alias-direct/repro.lit
```

```litex
# Known gap: K001
# Desired success: true
# See todo.md; runner checks observed behavior explicitly.

have fn f(x R) R = x + 1
let g = f
g(4) = 5
```

- Before the repair: exit 1, JSON `success: false`.
- Desired after repair: exit 0, JSON `success: true`. Keep the same assertion and avoid introducing trust.
- Actual CLI result, process status, and original command: [observed.json](observed.json).

## Evidence and next action

The recorded behavior is reproduced. Source links below are investigation entry points, not proof that a particular function contains the defect.

- Observed: Function definition and alias binding succeed; direct evaluation equality rejects with `search_proof`.
- Expected / checked control: The canonical function body should justify the call through its transparent alias. The checked control uses `g(4) = f(4)`, then `f(4) = 5`, then `g(4) = 5`.
- Resolution: the fact-based special-property index and stored function-equality path now justify direct body reduction. Wrong-arity/carrier/value and rollback controls remain executable in `special_property_tests`.
- Primary blocker: `kernel_problem`.

Source entry points:

- [src/execute/execute_fact_stmt/verify_atomic_fact/verify_equality/by_object_definition/by_identifier/by_let_obj.rs](../../../../../src/execute/execute_fact_stmt/verify_atomic_fact/verify_equality/by_object_definition/by_identifier/by_let_obj.rs)

## Controls and acceptance

- Primary positive controls: [let_obj_stmt.lit](../../../let_obj_stmt.lit).
- Rejection controls:
  - [duplicate-name.lit](../../../negative/let_obj_stmt/duplicate-name.lit)
  - [undefined-value.lit](../../../negative/let_obj_stmt/undefined-value.lit)
  - [zero-divisor.lit](../../../negative/let_obj_stmt/zero-divisor.lit)

```bash
python3 examples/test_statements/run.py --leaf LetObjStmt
```

The runner now requires the desired success for this same source. The dedicated acceptance record is maintained in the suite's experience area; the original failure source/capture remains here for provenance.

Back to [issue index](../../README.md).
