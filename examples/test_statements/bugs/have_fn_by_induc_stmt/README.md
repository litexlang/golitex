# HaveFnByInducStmt

## Task context

- Task: per-statement regression suite requested on 2026-10-01; issue organization requested on 2026-10-02.
- Scope: HaveFnByInducStmt issue index.
- Related workspace: golitex.

Primary fixture: [have_fn_by_induc_stmt.lit](../../have_fn_by_induc_stmt.lit).

## Open issues

- [ ] [K004: Recursive call under addition does not reduce to its value](K004-recursive-call-under-addition/README.md)

Current proof-search limitation: [explicit recursive equality chain](limitations.md).

```bash
python3 examples/test_statements/run.py --leaf HaveFnByInducStmt
```

Back to [issue index](../README.md).
