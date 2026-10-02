# TrustHaveStmt

## Task context

- Task: per-statement regression suite requested on 2026-10-01; issue organization requested on 2026-10-02.
- Scope: TrustHaveStmt issue index.
- Related workspace: golitex.

Primary fixture: [trust_have_stmt.lit](../../trust_have_stmt.lit).

## Output issue

- [ ] [D001: missing space in displayed trust-have](D001-missing-display-space/README.md)

## Related investigations

- [K006](../def_template_stmt/K006-strict-template-trust-have/README.md): Direct strict trust-have rejects as expected; the reproduced inconsistency is in template nesting.

Current restrictions and strict policy: [limitations.md](limitations.md).

```bash
python3 examples/test_statements/run.py --leaf TrustHaveStmt
```

Back to [issue index](../README.md).
