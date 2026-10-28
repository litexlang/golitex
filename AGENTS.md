# Repository working agreements

## Start with the Agent Guide

Read [docs/AgentGuide.md](docs/AgentGuide.md) before iterative Litex proof work.
Its first rule is to open `-session` for iterative Litex authoring and keep the
same live process after a normal statement failure, retaining earlier accepted
definitions and facts. Never rerun from the beginning after adding a few new
lines. It includes a checked comparison and the exact restart/replay boundary.
Apply the `golitex-repository-policy` skill for the full repository working policy.

## Comparison and experiment READMEs

Write READMEs for comparisons, benchmarks, experiments and their supporting
source directories in English. Use English for headings, prose, table labels,
diagram labels and explanatory code comments. Preserve exact mathematical
code, measurements and material scope qualifications when translating.

## Approval before adding documentation

Obtain the user's explicit approval before adding, copying, moving, or generating
files into documentation directories (`docs/` or `documents/`). A general request
to implement, fix, or design something is not approval for that destination.
Honor destination-specific approval already given within its stated scope;
obtain further approval before expanding that scope.

Keep temporary design documents, exploratory design notes, and design drafts
under the repository-root `scripts/` workspace, such as
`scripts/<task>/.draft/`. Placing them in `docs/` or `documents/` requires the
user's explicit approval. This rule overrides generic draft-location and
documentation-publication advice for these artifacts.

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

## Unambiguous public mathematical names

The maintainer explicitly forbids conflicting public mathematical names.
Each public operation name must have one fixed mathematical and parameter
contract. Never use argument count or argument types to select between
different operations, approaches, or scalar/vector contracts under one name.
Shared LaTeX notation is not authorization for a shared Litex operation name.
Check existing declarations and reserved names before proposing a new name.

`lim(a)` is exclusively the one-argument real sequence selector.
`fn_lim(f,x0)` is exclusively the two-argument finite-point unary real function
selector. The former `lim(f,x0)` spelling is rejected, with no compatibility
overload. Multivariable `lim` and scalar/vector `differential` overload proposals
have been withdrawn. Track the verified naming contract and future distinct
names in `scripts/litex_limit_designs/unambiguous-math-names.md`.
This instruction overrides older skills/contracts that require preserving
the overloaded spelling.

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
