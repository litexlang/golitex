# ByEnumerateFiniteSetStmt

## Task context

- Task: per-statement regression suite requested on 2026-10-01; issue organization requested on 2026-10-02.
- Scope: ByEnumerateFiniteSetStmt issue index.
- Related workspace: golitex.

Primary fixture: [by_enumerate_finite_set_stmt.lit](../../by_enumerate_finite_set_stmt.lit).

## Open issues

- [ ] [K007-enumerate: Enumeration proof bodies cannot use their quantified binder](K007-enumeration-binder-proof-body/README.md)
- [ ] [K009-enumerate: Enumeration does not discharge conditional targets using their premises](K009-conditional-enumeration-goal/README.md)
- [ ] [K010: Arithmetic target over a displayed finite numeric carrier fails enumeration](K010-enumeration-arithmetic-carrier/README.md)

```bash
python3 examples/test_statements/run.py --leaf ByEnumerateFiniteSetStmt
```

Back to [issue index](../README.md).
