# DefStructStmt: current boundaries

## Task context

- Task: per-statement regression suite requested on 2026-10-01; issue organization requested on 2026-10-02.
- Scope: DefStructStmt restriction and tooling observations.
- Related workspace: golitex.

These are explicit implementation restrictions, documented policy, or tooling drift. They are not counted among the ten open issue groups. If support is intended, make that decision before changing the existing rejection contract.

### Input: `struct Single:` with only `x R`

- Observed boundary: Parse error: `struct definition expects at least two fields`.
- Supported route: Two-field plain and parametric structs.
- Existing reproductions: [single-field-is-currently-unsupported.lit](../../negative/def_struct_stmt/single-field-is-currently-unsupported.lit).

Malformed initial attempts and unsupported shorthand remain in the chronological journal; they are not silently promoted to confirmed bugs.

Back to [issue index](../README.md).
