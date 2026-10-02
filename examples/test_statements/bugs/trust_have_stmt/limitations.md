# TrustHaveStmt: current boundaries

## Task context

- Task: per-statement regression suite requested on 2026-10-01; issue organization requested on 2026-10-02.
- Scope: TrustHaveStmt restriction and tooling observations.
- Related workspace: golitex.

These are explicit implementation restrictions, documented policy, or tooling drift. They are not counted among the ten open issue groups. If support is intended, make that decision before changing the existing rejection contract.

### Current strict-mode contract

This is a checked policy boundary, not an additional bug. With `-strict` the CLI rejects this input:

```litex
# Boundary: strict-trust-have-rejected
# Owner: TrustHaveStmt

trust have x R:
    x = 1
```

Runnable control: [strict-trust-have-rejected.lit](../../boundaries/strict-trust-have-rejected.lit).

Malformed initial attempts and unsupported shorthand remain in the chronological journal; they are not silently promoted to confirmed bugs.

Back to [issue index](../README.md).
