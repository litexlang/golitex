# DefTemplateStmt

## Task context

- Task: per-statement regression suite requested on 2026-10-01; issue organization requested on 2026-10-02.
- Scope: DefTemplateStmt issue index.
- Related workspace: golitex.

Primary fixture: [def_template_stmt.lit](../../def_template_stmt.lit).

## Open issues

- [ ] [K002: Template member loses its usable carrier fact](K002-template-member-carrier/README.md)
- [ ] [K006: Strict mode accepts trust-have inside a template](K006-strict-template-trust-have/README.md)

```bash
python3 examples/test_statements/run.py --leaf DefTemplateStmt
```

Back to [issue index](../README.md).
