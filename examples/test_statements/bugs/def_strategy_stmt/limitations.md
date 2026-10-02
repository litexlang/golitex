# DefStrategyStmt: current boundaries

## Task context

- Task: per-statement regression suite requested on 2026-10-01; issue organization requested on 2026-10-02.
- Scope: DefStrategyStmt restriction and tooling observations.
- Related workspace: golitex.

These are explicit implementation restrictions, documented policy, or tooling drift. They are not counted among the ten open issue groups. If support is intended, make that decision before changing the existing rejection contract.

### Restored proof statements (2026-10-02)

`by def` and other normal statements now execute in the strategy's local forall
scope after goal WD, with final conclusion verification and failure rollback.
The former fact-only boundary was a migration omission, confirmed against
legacy `execution/strategy_execution.rs`. The positive `strategy-proof-control`
case and negative `false-nested-proof` case cover the changed boundary.
See [strategy_nested_proof.lit](../../../stmt_nodes/definition/strategy_nested_proof.lit)
for local have/claim/witness/obtain steps and later root-name reuse.

Malformed initial attempts and unsupported shorthand remain in the chronological journal; they are not silently promoted to confirmed bugs.

Back to [issue index](../README.md).
