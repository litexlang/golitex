# Repository working agreements

## Start with the Agent Guide

Read [docs/AgentGuide.md](docs/AgentGuide.md) before iterative Litex proof work.
Its first rule is to keep one live Session after a normal statement failure;
it includes a checked example and the exact restart/replay boundary. Apply the
`golitex-repository-policy` skill for the full repository working policy.

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
