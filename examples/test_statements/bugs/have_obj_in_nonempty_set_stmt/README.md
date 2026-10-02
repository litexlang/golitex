# HaveObjInNonemptySetStmt

## Task context

- Task: per-statement regression suite requested on 2026-10-01; issue organization requested on 2026-10-02.
- Scope: HaveObjInNonemptySetStmt issue index.
- Related workspace: golitex.

Primary fixture: [have_obj_in_nonempty_set_stmt.lit](../../have_obj_in_nonempty_set_stmt.lit).

## Related investigations

- [K002](../def_template_stmt/K002-template-member-carrier/README.md): Related template-wrapped object declaration. The failing reproducer is template membership, not a standalone declaration.

```bash
python3 examples/test_statements/run.py --leaf HaveObjInNonemptySetStmt
```

Back to [issue index](../README.md).
