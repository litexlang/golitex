# ReleaseAxiomOfChoiceStmt: current boundaries

## Task context

- Task: per-statement regression suite requested on 2026-10-01; issue organization requested on 2026-10-02.
- Scope: ReleaseAxiomOfChoiceStmt restriction and tooling observations.
- Related workspace: golitex.

These are explicit implementation restrictions, documented policy, or tooling drift. They are not counted among the ten open issue groups. If support is intended, make that decision before changing the existing rejection contract.

### Current strict-mode contract

This is a checked policy boundary, not an additional bug. With `-strict` the CLI accepts this input:

```litex
# Boundary: strict-choice-allowed
# Owner: ReleaseAxiomOfChoiceStmt

release axiom_of_choice: set {{1}}:
    forall A {{1}}:
        $is_nonempty_set(A)
```

Runnable control: [strict-choice-allowed.lit](../../boundaries/strict-choice-allowed.lit).

Malformed initial attempts and unsupported shorthand remain in the chronological journal; they are not silently promoted to confirmed bugs.

Back to [issue index](../README.md).
