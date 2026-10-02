# DefStrategyStmt: current boundaries

## Task context

- Task: per-statement regression suite requested on 2026-10-01; issue organization requested on 2026-10-02.
- Scope: DefStrategyStmt restriction and tooling observations.
- Related workspace: golitex.

These are explicit implementation restrictions, documented policy, or tooling drift. They are not counted among the ten open issue groups. If support is intended, make that decision before changing the existing rejection contract.

### Input: `strategy s:` with a `by def $P(x)` proof step

- Observed boundary: `def_strategy` rejects; the body currently uses the fact-only proof-step path.
- Supported route: The equivalent direct `$P(x)` proof step.
- Existing reproductions: [proof-control-in-strategy-is-unsupported.lit](../../negative/def_strategy_stmt/proof-control-in-strategy-is-unsupported.lit).

Malformed initial attempts and unsupported shorthand remain in the chronological journal; they are not silently promoted to confirmed bugs.

Back to [issue index](../README.md).
