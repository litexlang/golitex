# ByForStmt

## Task context

- Task: per-statement regression suite requested on 2026-10-01; issue organization requested on 2026-10-02.
- Scope: ByForStmt issue index.
- Related workspace: golitex.

Primary fixture: [by_for_stmt.lit](../../by_for_stmt.lit).

## Open issues

- [x] [K007-for: Enumeration proof bodies cannot use their quantified binder](K007-for-binder-proof-body/README.md)
- [x] [K008 (explicitly unsupported): Advertised finite Cartesian-product enumeration is unsupported](K008-finite-cartesian-domain/README.md)
- [x] [K009-for: Enumeration does not discharge conditional targets using their premises](K009-conditional-for-goal/README.md)

```bash
python3 examples/test_statements/run.py --leaf ByForStmt
```

Back to [issue index](../README.md).

Resolved boundary repairs and remaining enumeration limits: [acceptance](../../experience/problem_notes/statement-boundary-repairs.md).
