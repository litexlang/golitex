---
name: litex-concept-modeler
description: Model a mathematical subject, textbook, chapter, or Litex module before proof writing by inventorying its concepts, separating semantic roles from Litex declaration forms and proof status, drafting ideal usable interfaces, and building a typed dependency DAG with source order, use probes, and visible trust or implementation gaps. Use when Codex must decide whether concepts are objects, functions, canonical selections, props, structs, templates, claims, or theorems; answer what the concepts should ideally mean; map how they depend on one another; create or update module-level math_collections.md; or prepare a definition-first architecture before substantial Litex translation, proof, library, or kernel work.
---

# Litex Concept Modeler

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

Model the mathematical world before proving facts inside it. Treat concept
classification, ideal interfaces, and dependency order as a required upstream
design pass rather than cleanup after proof writing.

## Core distinction

Never put `template`, object, `prop`, and `thm` into one flat ontology. Record
three separate axes:

1. **Semantic role**: carrier, object, function, canonical selection,
   relation, structure, declaration family, or mathematical result.
2. **Litex form**: builtin, parameter, `have`, `have fn`,
   `have fn ... by exist!`, `prop`, `struct`, `template`, direct fact,
   `claim`, `thm`, or `axiom`.
3. **Epistemic status**: designed, checked, axiomatic, trusted proof debt, or
   blocked by an exact syntax, kernel, library, existence, uniqueness, or
   well-definedness obligation.

`trust` is never a semantic role. Proof processes such as `witness`, `obtain`,
`by cases`, `by contra`, and `by induc` establish facts; they are not concepts.

Before producing a concept model, read both
[`references/concept-forms.md`](references/concept-forms.md) and
[`references/dependency-dag.md`](references/dependency-dag.md) completely.

## Scope and artifact gate

Identify the source of truth, module boundary, included material, excluded
material, and intended downstream consumers. Preserve source terminology,
theorem identity, carrier choices, and pedagogical order.

For an existing top-level module, read its single `README.md` and
`math_collections.md` before changing the model. For a new module that the user
asked to implement, create the pair in the module root. For a textbook, place
the pair beside
`scripts/textbooks_drafts/<Book>/litex.config`; keep them out of exports,
imports, and rendered chapter lists. Treat `textbooks/<Book>/` as the read-only
published snapshot unless the user explicitly requests publication.

- `README.md` describes only the currently implemented and verified public API.
- `math_collections.md` records the ideal mathematical spine, important
  intermediate concepts, dependencies, downstream uses, and allowable holes.
- A complete extraction inventory or coverage ledger is a working artifact,
  not the module manual. Put it in the repository's designated `scripts/` or
  planning workspace when one exists.

When creating `math_collections.md`, adapt
[`assets/math_collections.template.md`](assets/math_collections.template.md)
instead of inventing a new schema.

## Workflow

### 1. Inventory the mathematical vocabulary

Read the source front to back and collect:

- carriers, parameter domains, and ambient spaces;
- named objects, constants, sets, and selected values;
- functions, operations, constructors, sequences, and set-valued maps;
- predicates, relations, admissibility conditions, and side conditions;
- bundled structures and their laws;
- parameterized declaration families;
- definitions, axioms, lemmas, propositions, theorems, corollaries, and main
  results;
- notation or aliases that do not introduce new mathematics;
- proof moves, examples, and exercises, kept separate from concepts; and
- explicit assumptions, omitted proofs, and unresolved source ambiguity.

Do not assume one source noun maps to one declaration. Split a concept when
later mathematics needs distinct interfaces. For example, distinguish a
candidate-limit relation, convergence, uniqueness of limits, and the selected
limit function.

### 2. Classify by downstream use

For every important concept, first write one sentence answering:

> What does the source introduce, and how must later mathematics use it?

Then select its semantic role and Litex form. Use these probes:

- Later code writes a value directly -> object via `have`.
- Later code applies `f(x)` -> `have fn`, not only a `prop`.
- Later code asserts `$P(x)` -> `prop`.
- Later code projects named fields from packaged data -> `struct`, commonly
  paired with an `is_*` law predicate.
- Later code instantiates `\Name<S>` and the resulting declaration changes
  with `S` -> `template`.
- Later code needs the unique value satisfying a relation -> prove unique
  existence, then expose `have fn ... by exist!`.
- Later code should visibly cite an important named result -> `thm`.
- A result serves only nearby reasoning -> direct fact or `claim`.

Parameters alone do not make a declaration a template. A theorem is a fact
about concepts, not a substitute for defining them.

### 3. Draft the ideal interface

Design the mathematically correct interface before accommodating current
implementation limitations. For each core concept record:

1. ordinary mathematical meaning;
2. semantic role;
3. chosen Litex form and why the nearest alternative is wrong;
4. minimal parameters, domains, codomain, and definition body;
5. exact source anchor or conventional identity;
6. one immediate downstream use probe;
7. direct dependencies; and
8. remaining proof, existence, uniqueness, well-definedness, parser, library,
   or kernel obligation.

Do not weaken a function into a predicate, turn a parameterized family into a
local abbreviation, narrow a carrier, add the desired theorem conclusion to
an admissibility condition, or preserve an incompatible implementation behind
an alias, wrapper, compatibility predicate, `abstract_prop`, or `trust`.

If the ideal interface is unsupported, keep the ideal form in the design and
mark the exact blocker. Do not call an interface `checkable` until its real
definition and use probe pass the current verifier.

### 4. Build a typed dependency DAG

Create nodes for the important concepts and results. Label every edge with its
reason: signature, definition, well-definedness, structure law, existence,
uniqueness, canonical selection, proof, import, or trust/source dependency.

Produce both:

- the dependency DAG, which explains mathematical prerequisites; and
- an ordered build sequence, which is a topological order chosen to preserve
  the source's pedagogical order as far as possible.

Treat `template` as a parameterization mechanism around declarations, not a
fixed layer of the graph. Show `axiom`, imported trusted background, and
`trust` as visible boundary nodes or edges. Resolve accidental cycles by
finding the missing primitive interface or separating a relation from its
selected value; do not hide cycles through mutual wrappers.

### 5. Compare the model with existing code

When code already exists, audit each core declaration against the ideal model:

- same semantic kind, carrier, parameters, codomain, and source identity;
- same intended downstream use;
- no hidden strengthened premise or weakened conclusion;
- dependencies visible and namespace-qualified where appropriate; and
- proof/trust status accurately represented.

Use the repository's definition, relation, or fact graph output when available
to compare the actual dependency surface with the planned DAG. Classify drift
as a modeling error, missing interface, implementation limitation, proof debt,
or documentation drift before editing.

### 6. Verify the smallest interfaces, then hand off

Test minimal definition-plus-use-probe fragments in the real module context.
Do not begin bulk proof writing while foundational concept forms are unsettled.

When available, hand bounded downstream work to the matching skill:

- `litex-definition-modeler` for one ambiguous or blocked core interface;
- `litex-math-textbook-translator` for source extraction and chapter writing;
- `litex-proof-writer` for proofs after interfaces stabilize; hand over the
  shortest known natural-language proof spine and its named dependencies so
  the formal proof can be audited for abstraction-level redundancy;
- `todo_writer` for exact unresolved blockers during implementation.

Update the module `README.md` only after the implemented public interface and
representative use probes verify.

## Required output

Return or write, as the task requires:

1. a scope and source-of-truth statement;
2. a concept inventory with semantic role, chosen Litex form, source anchor,
   downstream use, and status;
3. ideal interface cards for the mathematical spine;
4. a typed dependency graph with a legend;
5. an ordered implementation sequence;
6. exact modeling decisions, blockers, and visible trust boundaries; and
7. the next bounded handoff, without silently starting unrelated proof work.

## Quality gates

Before completion, check:

- **Ontology**: no object, function, construction, or structure is disguised
  as a proposition.
- **Usability**: every core interface has a natural downstream use probe.
- **Fidelity**: carriers, theorem identity, source order, and mathematical
  meaning were not silently changed.
- **Dependency**: important prerequisites and trust boundaries are visible;
  the build order is acyclic.
- **Epistemic honesty**: checked, axiomatic, trusted, and blocked work are not
  conflated.
- **Implementation honesty**: current verifier limitations do not redefine the
  ideal mathematics.
