---
name: litex-kernel-engineer
description: Modify the Litex Rust kernel, parser, runtime, verifier, builtin rules, infer rules, well-definedness logic, standard library, diagnostics, tests, and examples. Use when Codex needs to implement a missing Litex capability, fix verifier behavior, add or audit mathematical rules, improve output explanations, or make blocked Litex code verifiable by changing core logic.
---

# Litex Kernel Engineer

## Critical: Repository Policy And Verifier Loop

- In the golitex repository, apply `$golitex-repository-policy` alongside this
  skill and read its canonical bundled policy completely. That repository
  policy overrides generic or older guidance here.
- Build current source once with `cargo build --release` and invoke
  `target/release/litex`; never use `target/debug/litex` for Litex work.
- For every iterative `.lit` edit to a registered target, start one
  `target/release/litex -compact -session -before <current-file.lit>` process.
  This loads the configured prefix before the target, excludes the target and
  later files, and enters the target file's environment whether it is empty,
  partial, or failing.
- Submit target statements from the first one in source order, one literal
  outermost `try:` block per regression, declaration, theorem, or small
  fragment. A successful block commits to the session; immediately write the
  accepted source back without the outer `try:`. A failed block rolls back
  only itself; correct and resubmit that block in the same process.
- Once a real proof, library, inference, syntax, or formulation blocker is
  identified, keep the intended statement, use the narrowest legal `trust`,
  record the debt, and continue. Do not spend further proof-search iterations
  unless the user asks to remove that trust.
- Restart only when the process exits or cannot accept another frame, the
  registered prefix deliberately changes, or an already committed declaration
  must be replaced under the same name. Replay the target from its first
  statement after a restart. Record an unexpected unusable session as
  `kernel_problem`.
- Use `target/release/litex -compact -f <current-file.lit>` for a clean
  baseline, checkpoint, or final artifact gate. Use `-isolated -f` only for an
  intentionally standalone repro.
- Optionally use
  `target/release/litex -compact -f <current-file.lit> -trust-before-line <X>`
  as a disk-first suffix preview or fallback, never as the default loop. `X`
  must be the exact physical header line of the first changed or
  not-cleanly-verified top-level statement; move it backward after any earlier
  edit. The prefix is parsed and registered but skips well-definedness and
  proof verification, so dependent suffix results are `indirect_trust` and the
  run is not `checkable`. It is incompatible with `-session`, `-r`, and
  `-strict`; always finish with a clean `-f`.
- Reserve `target/release/litex -compact -r <module>` for an explicit complete
  module or repository gate. Rust changes still require the smallest relevant
  `cargo test --release ...` followed by the required broader release test;
  never use the unoptimized default profile for this workflow.

## Workflow

1. Reproduce the failing Litex snippet first, ideally in `examples/tmp.lit`.
2. Read the nearby Rust code before editing.
3. Decide whether the blocker belongs to syntax, parser, runtime, verifier, builtin rule, infer rule, stdlib, or diagnostics.
4. Make the smallest behavior change that matches existing architecture.
5. Add or update focused examples/tests.
6. Run the smallest relevant test, then the broader relevant test.

## Path Discipline

- Treat relative paths in user requests, including `tmp/...`, `examples/...`, `scripts/...`, and source-local output paths, as relative to the active Litex repository/workspace unless the user gives an absolute path. Do not interpret `tmp` as the system `/tmp` or `/private/tmp`. Use system temp directories only for build caches, isolated dependency installs, or when the user explicitly provides an absolute system-temp path.

## Repository Rules

- Use `use crate::prelude::*;` for repository imports.
- Import only `std` items directly.
- Prefer `.into()` for conversions instead of direct enum wrapping.
- Write code that is as simple and direct as possible. Do not introduce fancy Rust features when straightforward code works. Prefer plain, sequential control flow that reads from top to bottom over clever abstractions, dense iterator chains, macros, advanced type tricks, or compact syntax.
- Do not write logic in `mod.rs`.
- Prefer `new` constructors for structs.
- Put shared helpers in `helper.rs`, not at the top of major files.
- Keep edits scoped; do not refactor unrelated code.
- Do not introduce explicit lifetimes in functions or structs. In almost all cases, do not introduce templates. Before introducing a template, explain the need to the user and get confirmation.

## Rule Changes

For a builtin rule, include a short comment with the mathematical property and an example shape.

When adding a builtin rule, add or update a corresponding example under
`examples/01_proof_patterns/` when there is a natural proof-pattern location.
Keep the example small and runnable, and use it to show the intended user-facing
Litex proof shape for the rule.

For an infer rule, include a short comment with the triggering condition, inferred fact, and example shape.

Never add broad automation just to make one example pass. Preserve soundness boundaries and make proof debt visible.

## Litex Examples And Regression Snippets

When writing Litex examples, docs snippets, or regression `.lit` code, use the
smallest body that verifies in the real context. Do not add mechanical echoes:
a successful `by contra` need not be followed by its target again; a witness
need not be manually folded back into a named predicate when that is only for
closing the current target; and a known implication or iff can supply its
conclusion once its premise is present.

Do not remove facts by pattern alone. Keep explicit conjunction components
needed by `obtain`, package facts needed as later rewrite bridges, and function
equations that seed inference. Reproduce the shortened snippet as a focused
test before treating an example or regression as simplified.

## Tests

- Runnable `.lit` artifact: use the release CLI with `-f`; use `-r` only for
  the complete module gate.
- Litex example/docs harness: run
  `cargo test --release run_examples -- --nocapture` only when the harness is
  needed in addition to direct `.lit` verification.
- Mechanics draft chapters: run the live-policy command
  `cargo test --release run_mechanics_textbook_chapters -- --nocapture`, then
  inspect its target. While the harness still points at
  `textbooks/The-Mechanics-of-Litex-Proof`, also use the release CLI against
  `scripts/textbooks_drafts/The-Mechanics-of-Litex-Proof`; the harness alone
  validates only the published snapshot, not the draft. Record that runner
  drift as `kernel_problem`.
- Start with the smallest relevant release test. For whole-project, textbook,
  or performance-sensitive verification, build and run the release profile:
  `cargo build --release`, `cargo test --release <target> -- --nocapture`, or
  `target/release/litex -compact -r <module>` for a complete module gate.
- Do not report the duration of bare `cargo test` as Litex runtime performance:
  Cargo's default test profile is unoptimized and can be much slower than the
  shipped release binary.
- Parser/runtime/verifier/builtin/infer/well-definedness/output changes: run
  `cargo test --release run_all -- --nocapture` before treating complete.
- Report exact failing file, snippet, or line from test output before changing more code.

## References

- Read `references/kernel-map.md` for where common behavior lives.
- Read `references/rule-patterns.md` before adding builtin or infer rules.
- Read `references/test-matrix.md` before choosing validation commands.

## Persistent Task Ledger

For a kernel, verifier, stdlib, or diagnostics task that remains unfinished
after this turn, create or update `todo/<YYYY-M-D>/<project>.md` at the
repository root, using the current environment date without zero padding.
Record the minimal repro, affected files/rules, completed checkpoints, the
next smallest implementation step, and the exact focused/broad test commands.
This is a cross-turn execution ledger, not a replacement for source-local
translation blocker notes. Delete it only when the scoped change is complete
and its required verification has passed.
