# Repository working agreements

## Project identity and skill authoring

Litex is a **high-level language for formal mathematics**, designed to express
mathematical objects, definitions, statements and proofs close to ordinary
mathematical writing. It can serve as a frontend to proof systems including
**Lean, Coq, and Isabelle**. The native checker, proof evidence, backend
compilers and other outputs support this central language-level purpose.

Start design, implementation, examples, documentation and comparisons from
this identity. Preserve the intended mathematics across backend translations
and distinguish language semantics from backend-specific representations.
Separate architectural direction from implemented backend coverage, generated
output and successful independent checking.

Every new or revised Litex-related skill must state this identity near its
entry and apply its specialized workflow in service of it. Follow the shared
Project identity contract in `golitex-repository-policy`. The [verification walkthrough](examples/proof_search/README.md) documents a
checked example. Keep implemented output support separate from future backend
directions.

## Public documentation scope

Public documentation describes implemented syntax, mathematical contracts,
commands, examples and explicit support boundaries. Use direct technical
language. Do not add slogans, metaphors, language analogies, personal invention
narratives, speculative advantage claims or unfinished design proposals.
Keep development plans, historical repair/audit records and comparison
experiments in the ignored root `scripts/` workspace. Preserve their original
contents locally when retiring public material. Keep mathematical source
attribution and the assumptions, unsupported cases and limitations needed to
interpret a result. A documentation cleanup must not conceal a verification
failure or change the mathematics to make a claim appear stronger.

## Natural mathematical writing

Prefer `$integrable(f,a,b)` for integrability and `integral(f,a,b)=I` or the expression form `integ(x,a,b,E)=I` for an
integral value in new examples, explanations and mathematical proofs. When
shared verification can establish integrability from the function expression
or existing premises, write the integral equation directly. Keep necessary
integrability assumptions explicit for arbitrary functions.

Prefer ordinary mathematical properties and value equations over `has_...`
candidate predicates whenever the same statement is supported. For example,
write `deriv(f,x)=v` for a derivative value. Preserve all required domains and
existence conditions. Use candidate predicates when their explicit relation
is needed by the task or by a currently unsupported direct route.

## Calculus reference and updates

For calculus updates, first read the [Calculus chapter](docs/Manual.md#calculus)
and its [maintenance instructions](docs/Manual.md#calculus-maintenance).
Update the affected interfaces, domains, proof routes, examples and backend
coverage in that chapter together with the implementation or source library.

## Verification artifact lifecycle

For Litex-to-Lean work, keep the mathematical deliverables as canonical `.lit`
files paired with their actual compiler-generated `.lean` files. Keep necessary
compiler source and focused regression tests in their normal source locations.
Verify in place with the existing shared build and dependency caches.

Do not accumulate full source/workspace snapshots, copied executables, or
per-round verification archives. After completing a step, remove its disposable
test copies, temporary logs, and redundant task-local build outputs. Preserve
unrelated work and shared caches used by other tasks.

Before creating large additional artifacts, report their destination, expected
size, purpose, and cleanup plan, and obtain the user's agreement. Report any
temporary artifacts that remain when finishing or stopping a task. Do not
reconstruct temporary directories the user has deliberately deleted.

## Start with the Agent Guide

Read [docs/AgentGuide.md](docs/AgentGuide.md) before iterative Litex proof work.
Its first rule is to open `-session` for iterative Litex authoring and keep the
same live process after a normal statement failure, retaining earlier accepted
definitions and facts. Never rerun from the beginning after adding a few new
lines. It includes a checked comparison and the exact restart/replay boundary.
Apply the `golitex-repository-policy` skill for the full repository working policy.

## Shared verifier ownership and std task boundaries

The maintainer requires general expression membership verification and the
composition and reuse of its evidence to be owned by the shared `verify`
mechanism. WD consumers must use that common mechanism. Do not add a
scenario-specific WD branch, such as an order-only function-return fallback,
merely to make a particular standard-library theorem pass.

A request to build or expand `std` authorizes task-authored file additions,
modifications and removals only under the repository-root `std/` directory.
Changes outside `std/`, including kernel, parser, verifier, compiler, tests,
examples, documentation, configuration and inventories, require separate
explicit authorization. Read-only inspection and verification do not expand
the file-change scope. Supporting tests, documentation or inventory requirements
in another skill are not implicit exceptions to this restriction.

Try and verify explicit intermediate facts and existing source-library
constructions first. If a verifier limitation remains, report the exact
reproduction and discuss a separate, general verifier proposal; do not implement
that repair inside the std task or create blocker records outside the authorized
file scope. Do not weaken the mathematics or add unproved assumptions to hide
the limitation. This scope restriction overrides generic skill advice that
delegates local Rust repairs when the active task is std construction.

## Kernel framework lock (Tier 1 / Tier 2 / Tier 3)

Litex separates pure framework orchestration from growing mathematical/compiler
branches across three tiers enforced at Git commit and CI by
`.github/scripts/framework_guard.py` and `.github/framework_lock.json`:

- **Tier 1 — Frozen Backbone (SHA-256 locked, 27 files):** pure framework
  structs, scope/transaction stacks, top-level parser entry (`src/parse/parse.rs`),
  knowledge-base persistence/mount backbone (`src/knowledge_base/`,
  `src/run_module/import_kb.rs`), statement transaction boundary
  (`src/execute/exec_stmt.rs`), verification pipeline skeleton
  (`exec_fact_stmt.rs`, `verify.rs`, `verify_state.rs`, `verify_obj/entry.rs`,
  `verify_atomic_fact.rs`, `verify_well_defined.rs`, `verify_equal_fact.rs`,
  `search_equal_fact_proof.rs`, `verify_atomic_except_equality.rs`,
  `search_atomic_except_equality_fact_proof.rs`), and fact storage/inference
  pipeline (`store_fact_and_infer.rs`, `store_fact.rs`, `infer_fact.rs`).
  Normal feature, calculus-strategy, or compiler work must **never** edit Tier 1
  files. Any modification requires explicit maintainer approval, running
  `python3 .github/scripts/framework_guard.py --update-lock`, and committing with
  `ALLOW_FRAMEWORK_UNLOCK=1` (or interactive confirmation in
  `tools/commit_with_impact.sh`).
- **Tier 2 — Enum & Append-Only Dispatch Registries (21 files):** AST and
  proof-result enums plus pure routing tables (`src/parse/builtin_aliases.rs`,
  `src/execute/dispatch_stmt.rs`, `dispatch_obj_well_definedness.rs`,
  `dispatch_predicate_domain_wd.rs`, `search_equal_fact_by_builtin_strategy.rs`,
  builtin rule/strategy/theorem dispatchers, and KB enum codecs). Tier 2 files
  must never mutate environment stacks or transaction state, and normally grow
  only by appending new enum variants or match arms. Changes to existing entries
  produce an informational notice and proceed without additional confirmation.
- **Tier 3 — Feature & Domain Leaves:** all concrete statement implementations,
  domain WD modules, calculus/algebra rules and strategies, and read-only
  backend compilers (`src/compile_to_*`, `src/json_output/`, `src/reading/`,
  `src/extract_executable_code/`).

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
asks to delete them.

Do not create or retain independent Git repositories or Git history anywhere
under root `scripts/`. Remove nested `.git` metadata while preserving working
files. The golitex root `.git` must be retained. This explicit maintainer
instruction supersedes older rules requiring preservation of nested Git
history within `scripts/`.

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
