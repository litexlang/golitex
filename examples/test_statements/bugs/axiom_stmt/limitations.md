# AxiomStmt: current boundaries

## Task context

- Task: per-statement regression suite requested on 2026-10-01; issue organization requested on 2026-10-02.
- Scope: AxiomStmt restriction and tooling observations.
- Related workspace: golitex.

These are explicit implementation restrictions, documented policy, or tooling drift. They are not counted among the ten open issue groups. If support is intended, make that decision before changing the existing rejection contract.

### Current strict-mode contract

This is a checked policy boundary, not an additional bug. With `-strict` the CLI rejects this input before checking or storing its axiom interface:

```litex
# Boundary: strict-axiom-rejected
# Owner: AxiomStmt

axiom identity:
    ? forall x R:
        x = x
```

Expected: exit 1, top-level `success: false`, no executed statement results,
and a session error containing `` `axiom` is forbidden ``. This also applies to
axioms with true conclusions: use a checked `thm` in strict mode. Ordinary mode
still supports explicit axiomatic interfaces.

Runnable control: [strict-axiom-rejected.lit](../../boundaries/strict-axiom-rejected.lit).
The [false-equality tracer](../../../stmt_nodes/definition/strict_axiom_policy.lit)
preserves the former acceptance and current rejection commands.

Malformed initial attempts and unsupported shorthand remain in the chronological journal; they are not silently promoted to confirmed bugs.

Back to [issue index](../README.md).
