# K002: Template member loses its usable carrier fact

Status: resolved on 2026-10-02. Former blocker: `kernel_problem`.

The unchanged [repro.lit](repro.lit) now succeeds under the strict release CLI:

```bash
target/release/litex -lang en -strict -f examples/test_statements/bugs/def_template_stmt/K002-template-member-carrier/repro.lit
```

```litex
template<S nonempty_set>:
    have member S
\member<R> $in R
```

The declaration stores `forall S nonempty_set: \member<S> $in S`; the assertion
uses that forall through `cite_forall`. Both statements succeed, exit is 0,
top-level JSON `success` is true, and `session_error` is null. The historical
failure remains in [observed.json](observed.json); current evidence is in
[verified.json](verified.json).

The manifest runs the unchanged source as
`boundary/resolved-K002-template-member-carrier`. The primary
[fixture](../../../def_template_stmt.lit) checks direct membership and its
generalized form. [Solution and acceptance](../../../experience/problem_notes/K002-template-definition-facts.md)
cover the other template bodies, premise retention, strict trust rejection,
canonical identity, and transactional rollback. Wrong arity and multiple
body declarations retain their existing rejection controls.

```bash
python3 examples/test_statements/run.py --leaf DefTemplateStmt
```

Back to [issue index](../../README.md).
