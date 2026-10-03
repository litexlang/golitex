# Fact

## Task context

- Task: per-statement regression suite requested on 2026-10-01; issue organization requested on 2026-10-02.
- Scope: Fact issue index.
- Related workspace: golitex.

Primary fixture: [fact.lit](../../fact.lit).

## Open issues

No original K-number Fact issue remains open in this inventory. A broader
[finite-cardinality carrier observation](kernel_gate_2026-10-03.md) remains under diagnosis. K005's explicit proof and
its [solution](../../experience/problem_notes/K005-classified-negative-existence-contra.md)
are accepted; the bare automatic shortcut remains a documented limitation.

The former internal `known_only` control now passes; its [recheck and historical failure](../../experience/problem_notes/known-only-control-recheck.md) remain in experience records, rather than the open bug inventory.

Current restrictions and strict policy: [limitations.md](limitations.md).

```bash
python3 examples/test_statements/run.py --leaf Fact
```

Back to [issue index](../README.md).
