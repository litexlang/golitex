---
name: litex-definition-modeler
description: Choose and verify the right Litex form for mathematical definitions. Use when translating a definition, construction, notation, or reusable interface from a textbook, dataset, or natural-language problem and deciding between prop, have, have fn, have fn by exist!, and template; especially when a draft may incorrectly turn a function or parameterized construction into a prop.
---

# Litex Definition Modeler

## Critical: Repository Policy And Verifier Loop

- In the golitex repository, apply `$golitex-repository-policy` alongside this
  skill and read its canonical bundled policy completely. That repository
  policy overrides generic or older guidance here.
- Build current source once with `cargo build --release` and invoke
  `target/release/litex`; never use `target/debug/litex` for Litex work.
- For every iterative edit to a registered target, start one
  `target/release/litex -compact -session -before <current-file.lit>` process.
  This loads the configured prefix before the target, excludes the target and
  later files, and enters the target file's environment whether it is empty,
  partial, or failing.
- Submit target statements from the first one in source order, one literal
  outermost `try:` block per definition, use probe, or small related fragment.
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

Model definitions before proving downstream theorems. Produce a usable Litex
interface, not merely a proposition that describes the intended object.

## Module documentation gate

Before creating a top-level module or adding or changing one of its core
mathematical interfaces, read its single `README.md` and
`math_collections.md`. Create the pair in the module root when this is a new
module; for a textbook module, that root is
`scripts/textbooks_drafts/<Book>/`, beside `litex.config`. Treat
`textbooks/<Book>/` as the read-only published snapshot unless the user
explicitly requests publication. Do not create separate copies for each
submodule or source file. Keep a textbook pair out of Litex exports and
rendered chapter lists.

Use `README.md` as the factual map of the currently implemented public API.
Use `math_collections.md` as a lightweight mathematical manual for the
important concepts and intermediate nodes: their meaning, ideal Litex form,
representative signature, dependencies, downstream uses, and allowable proof
holes. Read [references/module-documentation.md](references/module-documentation.md)
for the expected contents and workflow.

Compare a candidate definition with the ideal shape in
`math_collections.md`. If they differ, decide whether the code misunderstood
the mathematics or the design note should change. Fix the code in the first
case; update the design note first in the second. Never keep incompatible
forms through a wrapper, alias, compatibility predicate, `abstract_prop`, or
`trust`.

A hole may defer a proof, existence argument, uniqueness argument, or
well-definedness proof behind a clear usable interface. It may not replace the
decision that a source concept is a function, object, template, relation, or
builtin.

## Definition gate

Before writing Litex, state in one sentence what the source introduces and how
later mathematics must use it. Then select exactly one primary form:

| Source role | Litex form |
| --- | --- |
| A property, relation, or condition | `prop` |
| A named object with a given value or type | `have` |
| A map with an explicit formula, cases, or recursive rule | `have fn` |
| A canonical value selected by proven unique existence | `have fn ... by exist!` |
| A reusable declaration family whose resulting type/object/function varies with parameters | `template` |

Use `prop` only when later code needs to assert a condition. Do not use it
when later code must apply a new function, refer to a selected value, or
instantiate a parameterized declaration.

## Function-vs-prop gate

Do not classify a named mathematical interface from its grammatical shape
alone. Before choosing `prop`, check how the source object is introduced and
how later mathematics must use it:

- A source-defined map, set-valued map, sequence, or formula-producing object
  is `have fn` when callers must write an application such as `f(x)` or
  `mZ(m)`.
- A statement about a candidate, such as divisibility, closeness, continuity,
  or having a derivative, remains a `prop`. If later mathematics needs the
  selected value, expose a separate `have fn` interface rather than changing
  the relation into a function.
- Preserve the source name, parameter domains, and codomain. Do not silently
  narrow `Z` to `N`, rename a conventional notation, or move a domain
  restriction into an unrelated predicate.
- For a set-valued function, type the set-builder variable as an element of
  the returned carrier. A function returning `power_set(Z)` normally uses
  `{x Z: ...}`, not `{x power_set(Z): ...}`.
- Check that every defining parameter occurs in the body. A parameter-free
  body is evidence that the candidate is describing the wrong concept.

When the source wording and the downstream use disagree, preserve the
source-facing construction and report the exact unresolved interface rather
than weakening it to a `prop`.

Read [references/construct-selection.md](references/construct-selection.md)
when the choice is non-obvious, involves a textbook definition, or needs an
anti-pattern comparison.

## Required output

For each modeled definition, provide:

1. **Semantic role** — property, object, function, canonical selection, or
   declaration family.
2. **Chosen form** — the Litex construct and one reason the nearest
   alternative is wrong.
3. **Minimal interface** — parameter domains, codomain when applicable, and
   the smallest definition body.
4. **Use probe** — one immediate later use: assert a `prop`, apply a
   function, cite a selected value, or instantiate a template.
5. **Status** — `checkable` only after the real verifier succeeds; otherwise
   `blocked` with the exact missing formula, codomain, existence, uniqueness,
   parser, or library obligation.

For module-level core work, also report how the definition compares with
`math_collections.md` and which downstream consumers its use probe covers.
After verification, keep the module `README.md` aligned with the actual public
interface.

## Construction discipline

- Preserve the source's construction boundary. If it says “define \(f\)”,
  “let \(d(x,y)\)”, “the unique value”, or “for every \(S,n\), introduce”,
  start from `have fn`, `have fn by exist!`, or `template`, not `prop`.
- Keep a relation and its selected value distinct. A relation such as
  `has_derivative_at(..., L)` may be a `prop`; the derivative value is a
  separate `have fn ... by exist!` when uniqueness is available.
- Make a function's domain, codomain, and restricted-domain hypotheses
  explicit. Do not hide a nonzero denominator or a membership condition in a
  later theorem.
- Never smuggle a theorem's intended conclusion into a premise, condition
  predicate, or helper interface. A condition must describe independently
  meaningful admissible data; state and prove the desired result as the
  theorem's conclusion instead.
- Function types are exact: never retype a larger-domain function through a
  compatibility predicate. If a `prop` expects `f fn(x E) T` and the available
  function is `g` on a larger domain, pass `fn(x E) T {g(x)}`. This is the
  explicit restriction value `g | E`; it keeps the domain visible at the call
  site.
- Use `template` only when parameters change the declaration itself and
  callers should instantiate it. Do not use a template merely to abbreviate
  one local property.
- If a required construction cannot yet be verified, keep its intended
  `have fn` or `template` shape in the explanation and return `blocked`.
  Never replace it with a `prop` just to make the translation look complete.
- If a helper relation or imported definition is used inside a construction,
  confirm that the exact helper is available in the current environment. Do
  not call a use probe verified merely because the formula looks plausible.

## Verification loop

1. Inspect nearby Litex definitions and current syntax before writing a
   nontrivial interface.
2. Put the minimal definition and its use probe in the repository's designated
   scratch context, or test literal fragments in a persistent Litex `try:`
   loop.
3. Read the exact verifier result and make the next smallest correction.
4. Hand the verified definition plus use probe to the proof-writing or
   textbook-translation workflow for theorem proof and source-facing prose.

## Persistent Task Ledger

When definition/interface work spans several items or cannot be completed in
this turn, create or update `todo/<YYYY-M-D>/<project>.md` at the repository
root, using the current environment date without zero padding. Record the
definition's semantic role, attempted interface/use probe, exact remaining
obligation, next action, and verification command. Keep source-local blocker
notes as well when they apply; delete this task ledger only after the scoped
work is complete and verified.
