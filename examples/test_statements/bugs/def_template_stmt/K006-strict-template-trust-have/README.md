# K006: Strict mode accepts trust-have inside a template

Status: open. Primary blocker: `kernel_problem`.

## Task context

- Task: per-statement regression suite requested on 2026-10-01; issue organization requested on 2026-10-02.
- Scope: DefTemplateStmt / K006.
- Related workspace: golitex.

## Reproduction and captured result

[repro.lit](repro.lit) contains the unchanged source from `known_gaps/strict-template-trust-have.lit`. Run from the repository root:

```bash
target/release/litex -lang en -strict -f examples/test_statements/bugs/def_template_stmt/K006-strict-template-trust-have/repro.lit
```

```litex
# Known gap: K006
# Desired success: false
# See todo.md; runner checks observed behavior explicitly.

template<S set>:
    trust have hidden R:
        hidden = 1
```

- Current: exit 0, JSON `success: true`.
- Desired after repair: exit 1, JSON `success: false`. The strict rejection must identify forbidden trust-have, rather than an unrelated parser error.
- Actual CLI result, process status, and original command: [observed.json](observed.json).

## Evidence and next action

The recorded behavior is reproduced. Source links below are investigation entry points, not proof that a particular function contains the defect.

- Observed: With `-strict`, the template containing `trust have` returns exit 0 and `success: true`. The same trust-have outside a template returns exit 1 and the forbidden-under-strict session error.
- Expected / checked control: Strict mode advertises rejection of trust/trust-have. The template form should reach the same rejection boundary before the template is accepted.
- Follow-up: Audit the template execution path against the existing strict gate. Also retain the checked claim/sketch rejection controls. A protected Env/Runtime/AST change would require separate user authorization.
- Primary blocker: `kernel_problem`.

Source entry points:

- [src/execute/execute_def_template_stmt/exec_def_template_stmt.rs](../../../../../src/execute/execute_def_template_stmt/exec_def_template_stmt.rs)

## Controls and acceptance

- Primary positive controls: [def_template_stmt.lit](../../../def_template_stmt.lit).
- Rejection controls:
  - [two-template-bodies.lit](../../../negative/def_template_stmt/two-template-bodies.lit)
  - [wrong-template-arity.lit](../../../negative/def_template_stmt/wrong-template-arity.lit)

- Strict rejection control: [strict-trust-have-rejected.lit](../../../boundaries/strict-trust-have-rejected.lit)
- Strict rejection control: [strict-claim-trust-rejected.lit](../../../boundaries/strict-claim-trust-rejected.lit)
- Strict rejection control: [strict-sketch-trust-rejected.lit](../../../boundaries/strict-sketch-trust-rejected.lit)

```bash
python3 examples/test_statements/run.py --leaf DefTemplateStmt
```

The ordinary runner checks the recorded current behavior. When this reproduction changes, it must report a mismatch until its expectation is reviewed. To close the issue, run this same source to the desired outcome, preserve the nearest rejection controls, promote the repaired case into ordinary regression coverage, update [manifest.json](../../../manifest.json), and move the resolved note to the suite's experience records. For shared IDs, check every linked statement variant before closing the group.

Back to [issue index](../../README.md).
