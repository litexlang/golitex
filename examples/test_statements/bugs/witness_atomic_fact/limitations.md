# WitnessAtomicFact: current boundaries

## Task context

- Task: per-statement regression suite requested on 2026-10-01; issue organization requested on 2026-10-02.
- Scope: WitnessAtomicFact restriction and tooling observations.
- Related workspace: golitex.

These are explicit implementation restrictions, documented policy, or tooling drift. They are not counted among the ten open issue groups. If support is intended, make that decision before changing the existing rejection contract.

### Input: `witness $P(3) from 3` where `P(a R): exist! x R st {x = a}`

- Observed boundary: `witness_atomic` rejects; the implementation permits only ordinary exist clauses.
- Supported route: `witness exist! x R st {x = 3} from 3`; predicate folding followed by obtain is covered.
- Existing reproductions: [unique-exist-predicate-is-unsupported.lit](../../negative/witness_atomic_fact/unique-exist-predicate-is-unsupported.lit).

Malformed initial attempts and unsupported shorthand remain in the chronological journal; they are not silently promoted to confirmed bugs.

Back to [issue index](../README.md).
