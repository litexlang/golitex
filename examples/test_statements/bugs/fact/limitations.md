# Fact: current boundaries

## Task context

- Task: per-statement regression suite requested on 2026-10-01; issue organization requested on 2026-10-02.
- Scope: Fact restriction and tooling observations.
- Related workspace: golitex.

These are explicit implementation restrictions, documented policy, or tooling drift. They are not counted among the ten open issue groups. If support is intended, make that decision before changing the existing rejection contract.

### Input: `exist! x R st {x = 3}` alone

- Observed boundary: `search_proof` rejects; this search route does not synthesize the uniqueness proof.
- Supported route: Checked witness followed by the unique-exist assertion.
- Captured authoring evidence: [authoring.json](../../proof_journals/authoring.json).

Malformed initial attempts and unsupported shorthand remain in the chronological journal; they are not silently promoted to confirmed bugs.

Back to [issue index](../README.md).
