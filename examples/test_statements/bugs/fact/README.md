# Fact

## Task context

- Task: per-statement regression suite requested on 2026-10-01; issue organization requested on 2026-10-02.
- Scope: Fact issue index.
- Related workspace: golitex.

Primary fixture: [fact.lit](../../fact.lit).

## Open issues

- [ ] [K005: Explicit by-contra cannot target negative existence](K005-finite-negated-existence/README.md)

K005 is a category-2 local repair candidate whose scope remains under diagnosis; Codex owns the next action and checks under the maintainer's delegation. See the [classified suite todo](../../todo.md).

The former internal `known_only` control now passes; its [recheck and historical failure](../../experience/problem_notes/known-only-control-recheck.md) remain in experience records, rather than the open bug inventory.

Current restrictions and strict policy: [limitations.md](limitations.md).

```bash
python3 examples/test_statements/run.py --leaf Fact
```

Back to [issue index](../README.md).
