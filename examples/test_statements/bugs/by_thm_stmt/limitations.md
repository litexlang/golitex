# ByThmStmt: current boundaries

## Task context

- Task: per-statement regression suite requested on 2026-10-01; issue organization requested on 2026-10-02.
- Scope: ByThmStmt restriction and tooling observations.
- Related workspace: golitex.

These are explicit implementation restrictions, documented policy, or tooling drift. They are not counted among the ten open issue groups. If support is intended, make that decision before changing the existing rejection contract.

### Input: `by thm t(1):` with indented `1 = 1`

- Observed boundary: Parse error: `by thm: expected bare call or => <atomic fact>`.
- Supported route: `by thm t(1) => 1 = 1`; bare calls route to `ReleaseThmStmt`.
- Existing reproductions: [colon-selected-theorem-call-rejected.lit](../../boundaries/colon-selected-theorem-call-rejected.lit).

Malformed initial attempts and unsupported shorthand remain in the chronological journal; they are not silently promoted to confirmed bugs.

Back to [issue index](../README.md).
