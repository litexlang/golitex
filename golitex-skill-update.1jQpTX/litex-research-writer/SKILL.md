---
name: litex-research-writer
description: Write rigorous Litex documentation, research positioning, public explanations, reviewer packets, grant or funding applications, outreach emails, benchmark reports, soundness and scope notes, README copy, demos, and comparison material. Use when Codex needs to explain Litex to researchers, funders, students, AI-for-math readers, Lean/proof-assistant audiences, or general technical audiences.
---

# Litex Research Writer

## Critical: Repository Policy And Verifier Loop

- In the golitex repository, apply `$golitex-repository-policy` alongside this
  skill and read the live repository `AGENTS.md` completely. The live policy
  overrides generic or older guidance here.
- Build current source once with `cargo build --release` and invoke
  `target/release/litex`; never use `target/debug/litex` for runnable snippets.
- For every iterative edit to a registered snippet or demo target, start one
  `target/release/litex -compact -session -before <current-file.lit>` process.
  This loads the configured prefix before the target, excludes the target and
  later files, and enters the target file's environment whether it is empty,
  partial, or failing.
- Submit target statements from the first one in source order, one literal
  outermost `try:` block per documentation example or small related fragment.
  A successful block commits to the session; immediately write the accepted
  source back without the outer `try:`. A failed block rolls back only itself;
  correct and resubmit that block in the same process.
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
  baseline, checkpoint, or final snippet gate. Use `-isolated -f` only when
  the snippet file is intentionally standalone.
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
  demo or module gate. Never use default-profile `cargo test` as the Litex
  verifier; run the smallest genuinely required
  `cargo test --release ...` documentation harness separately.

## Core Positioning

Use this sentence as the strategic anchor unless the user asks for a different frame:

> Litex is not trying to replace Lean. It tests a different hypothesis: that a smaller, readable, fact-oriented formal language can make checked mathematics cheap enough for students, domain scientists, and AI agents to produce useful formal data at scale.

## Flagship Documentation Experience

When writing README, manual, Mechanics, demos, or other first-contact Litex
documents, optimize for bringing the reader into the Litex world, not for
explaining Litex from outside. The desired reader path is:

1. The syntax is readable.
2. A tiny fact can be checked.
3. Adding context makes more facts checkable.
4. The reader can define a concept.
5. The reader can build a small mathematical world.
6. The reader understands that Litex differs from Lean by offering a different
   proof interface, not merely by writing fewer tactics.

Audit the draft from the reader's emotional path. Ask: where would the first
friction or confusion appear; would a mathematically curious reader keep
reading; does each section produce a small sense of creation or verification;
does the Lean/Litex comparison reveal a real interface difference; does the
document make Litex feel inviting without overclaiming?

## Path Discipline

- Treat relative paths in user requests, including `tmp/...`, `examples/...`, `scripts/...`, docs paths, and output artifact paths, as relative to the active Litex repository/workspace unless the user gives an absolute path. Do not interpret `tmp` as the system `/tmp` or `/private/tmp`. Keep drafts, reports, generated outputs, and local scratch files inside the repo-local folder the user names.

## Writing Rules

- Prefer evidence over hype.
- Keep claims modest and auditable.
- Keep runnable Litex snippets minimal: do not show proof-body echoes that the
  verifier already derives from a preceding witness, contradiction, local
  claim, known implication/iff, or definition folding. Retain the visible
  theorem statement and any line that teaches the intended mathematical move.
- Validate any shortened snippet in its full local context. Do not omit
  conjunction components needed by `obtain`, package facts needed as rewrite
  bridges, or function equations that seed inference.
- Pair ambitious claims with artifacts: repo, verifier, examples, benchmark slice, CI, demo, soundness note, blocker taxonomy.
- For first-contact docs, start from a runnable tiny checked fact before abstract positioning.
- Grow examples by adding context: assumptions, named facts, definitions, then a small reusable world.
- Make each section create or verify something concrete; avoid long explanation-only stretches.
- Put Lean/proof-assistant comparison after the reader has seen the interface difference in action.
- Explain fewer tactics as a consequence of the interface, not as the main claim.
- State risks directly: trusted base, `trust`, builtin/infer rules, stdlib coverage, diagnostics, and AI-generated proof quality.
- Explain Litex as complementary to Lean/Coq/Isabelle, not as a replacement.
- Frame failed translations as useful blocker data, not hidden failures.

## Common Outputs

For reviewer-facing material, produce a short packet:

1. one-page executive summary;
2. killer demo path: natural problem -> Litex statement -> Litex proof -> verifier output -> trace/blocker;
3. benchmark table;
4. soundness/scope note;
5. 6-10 page technical proposal;
6. narrow outreach emails asking for risk-focused feedback.

## References And Assets

- Read `references/positioning.md` for audience-specific framing.
- Read `references/claims-risk.md` before making public claims.
- Read `references/reviewer-packet.md` for packet structure.
- Use templates in `assets/` when drafting summaries, soundness notes, demo scripts, and outreach emails.

## Persistent Task Ledger

When a Litex documentation, benchmark, or research artifact task has several
remaining stages, create or update `todo/<YYYY-M-D>/<project>.md` at the
repository root before ending the turn, using the current environment date
without zero padding. Record completed artifacts/evidence, remaining review or
verification work, and the next smallest action. Delete the ledger only once
the scoped task is complete and its claimed evidence has been checked.
