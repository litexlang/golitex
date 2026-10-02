# ReleaseRegularityAxiomStmt: current boundaries

## Task context

- Task: per-statement regression suite requested on 2026-10-01; issue organization requested on 2026-10-02.
- Scope: ReleaseRegularityAxiomStmt restriction and tooling observations.
- Related workspace: golitex.

These are explicit implementation restrictions, documented policy, or tooling drift. They are not counted among the ten open issue groups. If support is intended, make that decision before changing the existing rejection contract.

### Input: `release regularity_axiom({})`

- Observed boundary: `release_regularity` rejects because its existential member conclusion requires nonemptiness.
- Supported route: Singleton, pair, and triple set release.
- Existing reproductions: [empty-set-has-no-regularity-witness.lit](../../negative/release_regularity_axiom_stmt/empty-set-has-no-regularity-witness.lit).

### Current strict-mode contract

This is a checked policy boundary, not an additional bug. With `-strict` the CLI accepts this input:

```litex
# Boundary: strict-regularity-allowed
# Owner: ReleaseRegularityAxiomStmt

release regularity_axiom({1})
```

Runnable control: [strict-regularity-allowed.lit](../../boundaries/strict-regularity-allowed.lit).

Malformed initial attempts and unsupported shorthand remain in the chronological journal; they are not silently promoted to confirmed bugs.

Back to [issue index](../README.md).
