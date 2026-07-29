---
name: golitex-repository-policy
description: Apply the golitex repository's mandatory cross-cutting policy for all work in the repository, including localized trust, persistent session-before proof iteration, release gates, textbook draft/public boundaries, translation records and todos, Rust/kernel conventions, documentation, tests, examples, scripts, configuration, and general maintenance. Use whenever Codex reads, edits, verifies, reviews, diagnoses, or maintains anything in the golitex repository, and use it alongside every task-specific Litex skill.
---

# Golitex Repository Policy

Use this skill as a constraint layer alongside the task-specific Litex skill.
It does not replace proof writing, translation, modeling, kernel engineering,
research writing, or todo workflows.

## Required policy loading

1. Read
   [`references/golitex-agents.md`](references/golitex-agents.md) completely
   before taking task actions. It is the canonical detailed policy.
2. Treat a repository `AGENTS.md` as a bootstrap that activates this skill,
   not as a second copy of the detailed rules.
3. If a live repository instruction conflicts with the bundled policy, follow
   the live higher-priority instruction and report the drift so the skill can
   be refreshed.

User instructions take precedence over this skill. The golitex repository
policy takes precedence over generic or older workflow advice in another
Litex skill.

## Verification quick contract

- Use one release
  `target/release/litex -compact -session -before <current-file.lit>` process
  as the default iterative loop for a registered file.
- Submit target-file statements in source order, one literal outermost `try:`
  block at a time. Retry only the current failed statement in the same
  session. Write every accepted statement back without the outer `try:`.
- Use the narrowest source `trust` immediately after a real proof, library,
  inference, syntax, or formulation blocker is identified, record the debt,
  and continue.
- Use
  `target/release/litex -compact -f <current-file.lit> -trust-before-line <X>`
  only as an optional disk-first suffix preview or fallback. `X` must be the
  exact physical header line of the first changed or not-cleanly-verified
  top-level statement. Move it backward after any earlier edit.
- Treat the cutoff prefix as trusted, not verified: well-definedness and proof
  checks are skipped there, dependent suffix results carry
  `cli_trusted_prefix` / `indirect_trust`, and the run is never `checkable`.
- Finish a file with a clean release `-f` run without the cutoff. Reserve
  release `-r` for an explicit whole-module or whole-book gate.
- When a mandated Rust harness currently targets a different tree from the
  artifact named by the repository policy, still run the mandated command, but
  do not misreport its coverage. Add the smallest release CLI gate against the
  intended artifact and report the harness drift as `kernel_problem`.
