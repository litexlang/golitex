# RegisterTransitivePropStmt: current boundaries

## Task context

- Task: per-statement regression suite requested on 2026-10-01; issue organization requested on 2026-10-02.
- Scope: RegisterTransitivePropStmt restriction and tooling observations.
- Related workspace: golitex.

These are explicit implementation restrictions, documented policy, or tooling drift. They are not counted among the ten open issue groups. If support is intended, make that decision before changing the existing rejection contract.

### Input: `register reflexive:` with `? forall x R: $P(x, x)`

- Observed boundary: Parse error: every forall parameter type must be `set`; symmetric/transitive have the same restriction.
- Supported route: Set-carrier equality, subset, and conjunction definitions; false shaped laws also reject.
- Existing reproductions: [transitive-carrier-R.lit](../../negative/register_transitive_prop_stmt/transitive-carrier-R.lit), [transitive-carrier-N.lit](../../negative/register_transitive_prop_stmt/transitive-carrier-N.lit).

Malformed initial attempts and unsupported shorthand remain in the chronological journal; they are not silently promoted to confirmed bugs.

Back to [issue index](../README.md).
