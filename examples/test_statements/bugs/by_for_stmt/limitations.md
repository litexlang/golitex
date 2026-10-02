# ByForStmt: current supported scope

## Task context

- Task: remove K008 from bug records per the user's 2026-10-02 scope decision.
- Scope: finite enumeration carriers in ByForStmt.
- Related workspace: golitex.

## Cartesian carriers are currently excluded

Task: explicit user decision on 2026-10-02. This is not an open bug or a pending cart implementation request.

```litex
by for:
    ? forall p cart({1, 2}, {3, 4}):
        p = p
```

This input is expected to reject. Its fixture lives under [boundaries/unsupported-cartesian-for-domain.lit](../../boundaries/unsupported-cartesian-for-domain.lit).

Decision and prior evidence: [K008 record](../../experience/problem_notes/K008-cart-excluded.md).

Back to [statement folder](README.md) or [issue index](../README.md).
