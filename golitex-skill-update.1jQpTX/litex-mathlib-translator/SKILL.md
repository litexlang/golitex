---
name: litex-mathlib-translator
description: Translate Lean/mathlib interfaces, definitions, theorem statements, lemmas, namespaces, and reusable API slices into Litex standard-library code, examples, or translation workspaces. Use when Codex needs to port mathlib content to Litex, decide what Lean proof/library material should become Litex `thm`, `prop`, `trust`, builtin/infer-rule work, or stdlib blockers, and run a Litex verifier feedback loop for mathlib-derived translations.
---

# Litex Mathlib Translator

## Critical: Repository Policy And Verifier Loop

- In the golitex repository, apply `$golitex-repository-policy` alongside this
  skill and read the live repository `AGENTS.md` completely. The live policy
  overrides generic or older guidance here.
- Build current source once with `cargo build --release` and invoke
  `target/release/litex`; never use `target/debug/litex` for Litex work.
- For every iterative edit to a registered target, start one
  `target/release/litex -compact -session -before <current-file.lit>` process.
  This loads the configured prefix before the target, excludes the target and
  later files, and enters the target file's environment whether it is empty,
  partial, or failing.
- Submit target statements from the first one in source order, one literal
  outermost `try:` block per translated declaration, theorem, or small proof
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
  baseline, checkpoint, or final file gate. Use `-isolated -f` only for an
  intentionally standalone file.
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
  module or repository gate. Never use default-profile `cargo test` as the
  Litex verifier; run the smallest genuinely required
  `cargo test --release ...` harness separately.

## Why Translate Mathlib

Use mathlib as a standard-library roadmap, not as a repository to mechanically
port. The main value is that mathlib exposes mature choices about mathematical
interfaces, theorem families, namespace boundaries, and dependency pressure.

For Litex, the bottleneck is often not whether a single statement can be
expressed, but knowing which mathematical content is worth building next.
Treat each mathlib slice as a way to discover and prioritize Litex stdlib work:
definitions, theorem clusters, naming conventions, examples, infer rules,
builtin rules, diagnostics, and proof patterns.

## Core Principle

Translate the mathematics and reusable library surface, not Lean syntax or tactics.

Litex and Lean have different proof models. Lean often needs theorem calls for small algebra, arithmetic, coercions, rewriting, and tactic bookkeeping that Litex can handle directly through builtin rules, infer rules, pattern matching, and ordinary fact verification. Do not force Lean-shaped proofs into Litex. Use Lean/mathlib as a source of mathematical organization, theorem names, API coverage, and dependency ideas; write the Litex version in natural Litex style.

For a new top-level reusable Litex module, or when a mathlib slice changes one
of its core interfaces, read the module's single `README.md` and
`math_collections.md` before writing code. Keep `README.md` factual about the
implemented API; use `math_collections.md` as a lightweight mathematical
manual for important concepts, ideal Litex forms and downstream uses. Do not
create a pair per source file or namespace. When code and the manual differ,
repair the mistaken side before continuing rather than preserving both shapes
through wrappers, aliases, `abstract_prop`, or `trust`.

## Translation Meaning

Classify every item by what the Litex work actually achieved:

- `translated`: the mathematical statement or interface has a natural Litex formulation.
- `checkable`: the Litex statement and proof verify without `trust`.
- `blocked`: the failure reason is understood and recorded with a minimal reproduction or nearby note.

When a blocker is identified, keep the intended statement and use `trust` only
on the narrowest blocked step. Explain it in nearby notes, classify the primary
blocker as `trust` or `kernel_problem`, and continue making the surrounding
development explicit. A declaration containing `trust` is not `checkable`.

For large API slices, use a mainline-first refinement workflow. Do not try to
port every supporting lemma in dependency order before the useful interface can
run. First build the reusable mathematical surface and the examples that need
it; then isolate genuinely unproved, lengthy support facts as local named
theorem interfaces. Before putting any fact in a cite package, test its
statement directly in the real Litex context. If builtin or infer rules verify
it, use the fact directly: do not port or invent a `thm` wrapper merely so it
can be cited, and never add a trusted builtin duplicate to cite. Repetition and
the presence of a Lean theorem name do not make an elementary builtin fact
cite-worthy. If a simple expected fact fails, record the missing builtin,
infer, stdlib, or kernel support instead of hiding it as citation debt.

Put real shared vocabulary in a `*_vocab/main.lit` module with ordinary
`prop`/`have` definitions. Reserve a source-local cite package with named
`thm`/`claim` interfaces plus narrow `trust` for substantial facts that remain
unproved after one direct real-context attempt and whose deferred proof would
otherwise block the main API slice. Import cite packages with `import`; do not
duplicate real definitions as `abstract_prop` just because the cite module
cannot see the caller's local environment.

## Translation Target

Prefer translating:

- interfaces, definitions, predicates, structures, namespaces, and theorem statements;
- reusable theorems that add real mathematical library coverage;
- simple low-dependency lemmas that make later translations shorter;
- examples that pressure-test Litex standard-library gaps.

Usually skip:

- theorem-prover plumbing that Litex does not need;
- basic natural-number, integer, rational, algebraic, and order facts already handled by Litex builtin rules;
- Lean-specific coercion, simp, rewrite, decidability, instance, or tactic-support lemmas unless they expose a real Litex gap;
- proofs whose only purpose is to satisfy Lean automation but add no reusable Litex fact.

## Mapping Lean To Litex

- Lean `theorem` / `lemma` maps primarily to Litex `thm`.
- Use `prop` only for genuine mathematical predicates or structured properties, not as a wrapper just to name a `forall` fact.
- Call reusable theorem facts with `by thm name(args)` so hidden parameters are explicit at the call site.
- If a theorem is mathematically background knowledge and Litex cannot prove it yet, keep the `thm` statement and use local `trust` inside the theorem proof body as marked proof debt.
- Avoid the old pattern `prop wrapper(...): ...` plus `trust forall ... => $wrapper(...)` unless the wrapper is a real predicate users should reason about.
- Treat mathlib namespaces and file paths as an index, not as forced Litex
  directory structure. Choose Litex std modules by the natural Litex concept
  and existing std organization.
- If a mathlib name collides with a Litex builtin name, keyword, parser rule, or
  established std name, choose a Litex-native std name. Do not change the
  Litex kernel or parser just to preserve a mathlib spelling.

## Workflow

1. Pick a small vertical slice that can teach the stdlib roadmap.
2. Read the Lean statement and surrounding namespace/API to understand the mathematical intent.
3. Decide whether the item should be translated, skipped as Litex-builtin/Lean-specific, used only as roadmap context, or recorded as a blocker.
4. Write the simplest natural Litex statement first. Prefer `thm` for theorem names and direct facts for builtin arithmetic/order consequences.
5. Try a direct Litex proof using existing builtin rules, explicit intermediate facts, and existing `by thm` calls.
6. Once a real blocker is identified, add the smallest local `trust` needed
   inside the `thm` proof body, record it in nearby notes, and continue. Do not
   spend further proof-search iterations unless the user asks to remove it.
7. Run the verifier. Repair the next smallest failing step instead of mechanically importing more Lean lemmas.
8. Classify each item as `translated`, `checkable`, or `blocked`.
9. Convert repeated obvious proof needs into stdlib, builtin-rule, infer-rule, or diagnostics backlog items.

## Proof Style

- Prefer a minimal verified proof body over Lean-shaped scaffolding. Before
  adding a fact, test whether a preceding witness, local claim, contradiction,
  known implication/iff, definition unfolding, or predicate folding already
  closes the current target.
- Remove mechanical echoes such as restating a `by contra` target, folding a
  witness's existential body into a named predicate only to restate that
  predicate, or spelling out a conclusion already supplied by a known
  implication. Keep the theorem's public statement and meaningful
  mathematical intermediate steps.
- Do not compress blindly: an explicit component of a conjunction may be
  needed for `obtain`; a packaged fact may be a substitution bridge; and a
  function equation may seed inference. Validate the shorter form in the
  actual theorem context.
- Start with simple theorems and low-dependency API slices before large theorem clusters.
- Prefer Litex-readable mathematical steps over Lean tactic structure.
- Use explicit intermediate equalities, inequalities, witnesses, and theorem calls.
- Do not translate long chains of Lean helper lemmas when Litex can verify the final algebraic or order fact directly.
- When a Lean proof uses `simp`, `ring`, `linarith`, `norm_num`, or coercion lemmas, first try the corresponding direct Litex fact.
- When a theorem has parameters that do not appear in the final conclusion, keep them in the `thm` forall and pass them explicitly in `by thm` calls.

## Std Roadmap Use

Each mathlib slice should produce a stdlib gap map, not only `.lit` code.
When useful, record:

- mathlib source namespace or file;
- target Litex std module and chosen Litex name;
- status: `translated`, `checkable`, `blocked`, or `skipped`;
- proof debt, especially each remaining `trust`;
- downstream items that need this fact;
- next action: add std theorem, add definition, add example, add infer rule,
  add builtin rule, improve diagnostics, or reformulate.

Prioritize low-dependency, high-use std areas before deep theorem clusters:
`Nat`, `Int`, `Set`, `Finset`, `Fintype`, `Rat`, `Real`, `Complex`, `Trig`,
order, algebraic identities, divisibility, primes, finite sums/products, and
basic functions.

## Gap Classification

For every skipped or blocked mathlib/MIL item, use exactly one primary blocker
label: `trust` or `kernel_problem`. Explain the concrete cause in prose—such as
a missing definition, reusable theorem interface, long proof, namespace/file
placement issue, syntax/diagnostic gap, or suspected verifier behavior—without
inventing another coded taxonomy. Try one direct real-context formulation
before declaring the gap; once a non-kernel blocker is identified, keep the
intended interface, add the narrowest legal `trust`, record the debt, and
continue.

## Blockers And Notes

When translation fails, record the smallest reproduction and one primary blocker label:

`trust` or `kernel_problem`.

For work under `scripts/` or another translation workspace, maintain the nearby `todo.md`: add missing definitions, theorem families, infer rules, builtin rules, syntax issues, or diagnostic problems; remove items once implemented.

## Output Expectations

For a mathlib slice, report:

- what was translated and what was intentionally skipped;
- which items are checkable versus using local `trust` proof debt;
- any Litex stdlib/kernel gaps discovered;
- the verifier command run and its result.
## Persistent Task Ledger

For an unfinished mathlib slice, stdlib migration, or kernel follow-up, create
or update `todo/<YYYY-M-D>/<project>.md` at the repository root before ending
the turn, using the current environment date without zero padding. Include the
completed API items, skipped/blocked interfaces with their minimal examples,
the next smallest action, and verification commands. Keep source-local todo
and gap-map records too; delete this cross-turn ledger only after the scoped
work is complete and verified.
