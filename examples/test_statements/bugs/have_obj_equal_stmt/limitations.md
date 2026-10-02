# HaveObjEqualStmt: current boundaries

## Task context

- Task: per-statement regression suite requested on 2026-10-01; issue organization requested on 2026-10-02.
- Scope: HaveObjEqualStmt restriction and tooling observations.
- Related workspace: golitex.

These are explicit implementation restrictions, documented policy, or tooling drift. They are not counted among the ten open issue groups. If support is intended, make that decision before changing the existing rejection contract.

### Input: `have typed_p N_pos = 2`

- Observed boundary: `undefined name N_pos`; this is not a built-in carrier in the current tree.
- Supported route: `N`, `Q`, and an explicit positive finite carrier are tested.
- Captured authoring evidence: [authoring.json](../../proof_journals/authoring.json).

The undefined `N_pos` spelling is an authoring error, not a kernel bug.

Malformed initial attempts and unsupported shorthand remain in the chronological journal; they are not silently promoted to confirmed bugs.

Back to [issue index](../README.md).
