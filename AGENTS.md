# Repository working agreements

## Start with the Agent Guide

Read [docs/AgentGuide.md](docs/AgentGuide.md) before iterative Litex proof work.
Its first rule is to open `-session` for iterative Litex authoring and keep the
same live process after a normal statement failure, retaining earlier accepted
definitions and facts. Never rerun from the beginning after adding a few new
lines. It includes a checked comparison and the exact restart/replay boundary.
Apply the `golitex-repository-policy` skill for the full repository working policy.

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
