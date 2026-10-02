# K002: Template member loses its usable carrier fact

Status: open. Primary blocker: `kernel_problem`.

## Task context

- Task: per-statement regression suite requested on 2026-10-01; issue organization requested on 2026-10-02.
- Scope: DefTemplateStmt / K002.
- Related workspace: golitex.

## Reproduction and captured result

[repro.lit](repro.lit) contains the unchanged source from `known_gaps/template-member-carrier.lit`. Run from the repository root:

```bash
target/release/litex -lang en -strict -f examples/test_statements/bugs/def_template_stmt/K002-template-member-carrier/repro.lit
```

```litex
# Known gap: K002
# Desired success: true
# See todo.md; runner checks observed behavior explicitly.

template<S nonempty_set>:
    have member S
\member<R> $in R
```

- Current: exit 1, JSON `success: false`.
- Desired after repair: exit 0, JSON `success: true`. Keep the same assertion and avoid introducing trust.
- Actual CLI result, process status, and original command: [observed.json](observed.json).

## Evidence and next action

The recorded behavior is reproduced. Source links below are investigation entry points, not proof that a particular function contains the defect.

- Observed: Template declaration succeeds; `\member<R> $in R` rejects with `search_proof`. Instantiation itself is well-defined: `let selected = \member<R>` passes.
- Expected / checked control: Instantiating an object introduced with `have member S` should expose its instantiated membership. No checked membership repair was found; the canonical test demonstrates instantiation without claiming the missing fact.
- Follow-up: Audit template HaveObjInNonemptySet evidence and membership verification. Do not add an axiom or change the carrier. Positive control: `def_template_stmt.lit/parametric-nonempty-binding`.
- Primary blocker: `kernel_problem`.

Source entry points:

- [src/execute/execute_def_template_stmt/exec_def_template_stmt.rs](../../../../../src/execute/execute_def_template_stmt/exec_def_template_stmt.rs)

## Controls and acceptance

- Primary positive controls: [def_template_stmt.lit](../../../def_template_stmt.lit).
- Rejection controls:
  - [two-template-bodies.lit](../../../negative/def_template_stmt/two-template-bodies.lit)
  - [wrong-template-arity.lit](../../../negative/def_template_stmt/wrong-template-arity.lit)

```bash
python3 examples/test_statements/run.py --leaf DefTemplateStmt
```

The ordinary runner checks the recorded current behavior. When this reproduction changes, it must report a mismatch until its expectation is reviewed. To close the issue, run this same source to the desired outcome, preserve the nearest rejection controls, promote the repaired case into ordinary regression coverage, update [manifest.json](../../../manifest.json), and move the resolved note to the suite's experience records. For shared IDs, check every linked statement variant before closing the group.

Back to [issue index](../../README.md).
