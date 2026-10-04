# DefAbstractPropStmt: current boundaries

## Task context

- Task: per-statement regression suite requested on 2026-10-01; issue organization requested on 2026-10-02.
- Scope: DefAbstractPropStmt restriction and tooling observations.
- Related workspace: golitex.

These are implementation boundaries and policy observations, not additional open issue groups.

### Current strict-mode contract

The maintainer authorized allowing pure abstract declarations on 2026-10-04.
The old strict prohibition is removed; declaring a signature still proves no instances:

```litex
abstract_prop P(x)
# Neither $P(0) nor not $P(0) follows from this declaration.
```

Runnable positive control: [strict-abstract-prop-allowed.lit](../../boundaries/strict-abstract-prop-allowed.lit).
Executable rejection controls: [strict-abstract-instance-unproved.lit](../../boundaries/strict-abstract-instance-unproved.lit).
User `trust` / `trust have` remain forbidden, including template and nested proof forms.

Malformed initial attempts and unsupported shorthand remain in the chronological journal; they are not silently promoted to confirmed bugs.

Back to [issue index](../README.md).
