# Repository working agreements

## Start with the Agent Guide

Read [docs/AgentGuide.md](docs/AgentGuide.md) before iterative Litex proof work.
Its first rule is to open `-session` for iterative Litex authoring and keep the
same live process after a normal statement failure, retaining earlier accepted
definitions and facts. Never rerun from the beginning after adding a few new
lines. It includes a checked comparison and the exact restart/replay boundary.
Apply the `golitex-repository-policy` skill for the full repository working policy.

## Native mathematics inventory

For every addition, change, or removal on the native mathematical Obj/prop
roadmap that began with `lim`, update the same local inventory in the same task:
`scripts/litex_limit_designs/native-analysis-inventory.md`.
Record exact Obj/Fact interfaces, predicates, builtin rules and strategies,
reserved BT names/arities, source `thm` declarations, domains and WD, examples,
verification evidence, compatibility changes, and unsupported boundaries.
Distinguish new features from reused dependencies and plans from delivered work.
This inventory remains local-only under the scripts policy below.
Apply `litex-math-feature-maintainer` for this workflow; its maintained local
source is `scripts/litex_limit_designs/skills/litex-math-feature-maintainer/SKILL.md`.

## Local-only scripts workspace

The entire `scripts/` directory directly under this repository root is local-only.
Nothing under it may be added, committed, or pushed in the parent golitex
repository or published through its GitHub tree. There are no file or subtree
exceptions. Never use `git add -f` to bypass this rule.

Keep `/scripts/` ignored. Remove any accidentally tracked scripts paths from
parent-repository tracking; preserve local source files unless the user explicitly
asks to delete them. Preserve existing nested repositories and their histories.

Publish requested deliverables in the appropriate public directories, such as
`textbooks/`, `examples/`, `docs/`, or `showcases/`; do not expose the local
scripts workspace itself.

## Release scope: local textbooks are optional

Local textbook projects under `scripts/`, including Analysis, MIL, Mechanics,
LADR, and NTFB, are not required release gates. Do not run them merely because
the user asks whether Cargo tests pass or whether Litex is ready to release.
Run them only when the user explicitly requests textbook work or verification.
Their absence, failures, or timeouts alone must not be treated as release blockers.

This maintainer instruction overrides any bundled skill or older release note
that includes local textbooks in a mandatory full-release gate. In particular,
do not use `.github/scripts/predeploy_gate.py` as a mandatory release gate while
it includes these local textbook projects.
