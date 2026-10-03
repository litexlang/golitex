# Obj recheck: five recovered finite-set fold cases

Task: rerun the Obj corpus and identify surviving problems.
Scope: examples/test_objs; read-only verification and issue-record maintenance.
Baseline: current-source release audit at source c9b0a740cde136b1c2e8874de22ef68649db77dc678cd371c3fc233e873d9d92.

The unchanged invalid operation now rejects:

```litex
let r = finite_set_reduce({1, 2}, fn(x Z) Z {x}, fn(a, b Z) Z {a - b}, 0)
```

The operation lacks the associative/commutative laws required for unordered
finite-set reduction. The current WD owner checks both laws before admitting
the object. The observed failure is in the `let` declaration's WD requirements.
This closes the previous incorrect admission without weakening the input.

Four unchanged addition-fold fixtures now pass: singleton result 2, two elements
in either displayed order result 3, and nonidentity seed 10 result 13. Their
exact sources, exit statuses, original outcomes and current diagnostics are
preserved in [the audit journal](../../proof_journals/obj_audit_2026-10-03.json).
The full scan verifies all 284 rejection fixtures and all 99 owning positive
files. This audit did not implement the engine changes.

The current-source gate that captures all five recoveries is:

```sh
python3 examples/test_objs/run.py --report examples/test_objs/audit_2026-10-03_results.json
```

It builds successfully and exits 1 only for the 67 remaining direct fixtures.
No fixture in the recovered group fails its intended outcome. The WD owner is
`src/execute/execute_fact_stmt/well_defined_results/verify_obj/iterated.rs`.

The five recovered fixtures remain at their original manifest paths for
unchanged-source verification and historical comparison. They are removed from
the active todo, not skipped by the runner. The manifest still inventories 72
historical gap fixtures; 67 fail their intended result in the current audit.

Reusable diagnostic lesson: classify a failed direct assertion separately from
mathematical availability. This audit also verifies function composition with
intermediate values, set equality with `by extension`, fraction/min comparison
with a common denominator, tuple projection with an intermediate equality,
and singleton-set inequality with `by contra`. Those successes do not certify
the corresponding unchanged direct assertion or remove its automation gap.
