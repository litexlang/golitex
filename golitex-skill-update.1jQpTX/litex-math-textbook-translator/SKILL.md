---
name: litex-math-textbook-translator
description: Translate mathematical textbooks, lecture notes, and textbook-derived datasets into Litex. Use when Codex formalizes source definitions, propositions, or chapter slices; maintains the canonical scripts/textbooks_drafts module, paired source workspace, and explicitly published snapshot; chooses builtin, standard-library, or local formulations; tracks trust debt; or records library, kernel, syntax, or diagnostic gaps.
---

# Litex Math Textbook Translator

## Critical: Repository Policy And Verifier Loop

- In the golitex repository, apply `$golitex-repository-policy` alongside this
  skill and read its canonical bundled policy completely. That repository
  policy overrides generic or older guidance here.
- Build current source once with `cargo build --release` and invoke
  `target/release/litex`; never use `target/debug/litex` for Litex work.
- For every iterative chapter edit, start one
  `target/release/litex -compact -session -before <current-chapter.lit>`
  process. This loads the configured book prefix before the chapter, excludes
  that chapter and later files, and enters the chapter's environment whether
  it is empty, partial, or failing.
- Submit chapter statements from the first one in source order, one literal
  outermost `try:` block per source item or small proof fragment. A successful
  block commits to the session; immediately write the accepted source back
  without the outer `try:`. A failed block rolls back only itself; correct and
  resubmit that block in the same process.
- Once a real proof, library, inference, syntax, or formulation blocker is
  identified, keep the source-facing statement, use the narrowest legal
  `trust`, record the debt nearby and in the book workspace, and continue. Do
  not spend further proof-search iterations unless the user asks to remove
  that trust.
- Restart only when the process exits or cannot accept another frame, the
  registered prefix deliberately changes, or an already committed declaration
  must be replaced under the same name. Replay the chapter from its first
  statement after a restart. Record an unexpected unusable session as
  `kernel_problem`.
- Use `target/release/litex -compact -f <current-chapter.lit>` for a clean
  baseline, checkpoint, or final chapter gate.
- Optionally use
  `target/release/litex -compact -f <current-chapter.lit> -trust-before-line <X>`
  as a disk-first suffix preview or fallback, never as the default loop. `X`
  must be the exact physical header line of the first changed or
  not-cleanly-verified top-level statement; move it backward after any earlier
  edit. The prefix is parsed and registered but skips well-definedness and
  proof verification, so dependent suffix results are `indirect_trust` and the
  run is not `checkable`. It is incompatible with `-session`, `-r`, and
  `-strict`; always finish with a clean `-f`.
- Reserve `target/release/litex -compact -r <textbook-module>` for an explicit
  whole-book gate. Never use default-profile `cargo test` as the Litex
  verifier; run the smallest genuinely required `cargo test --release ...`
  harness separately.

## Artifact Boundary

Treat `scripts/textbooks_drafts/<Book>/` as the canonical development module.
Make all ordinary chapter `.lit`, `litex.config`, module `README.md`, and
`math_collections.md` edits and checks there. Initialize a missing draft once
with `scripts/textbooks_drafts/init_draft.sh <Book>`; never merge or copy a
public snapshot back over an existing draft.

Treat `textbooks/<Book>/` as the last manually published public snapshot. It is
read-only during ordinary writing and proof repair. Copy or synchronize a
draft into it only when the user explicitly requests publication.

Keep source material, translation records, todos, audits, experience notes,
generated Markdown, verifier captures, and temporary artifacts in the book's
existing paired workspace such as `scripts/Analysis/`, not in either module
tree. Use `/private/tmp` for disposable artifacts when appropriate.

## Module Documentation Gate

Treat the whole book or translation project as one top-level module, even when
it contains many chapter exports. Maintain exactly one `README.md` and one
`math_collections.md` in `scripts/textbooks_drafts/<Book>/` beside
`litex.config`; do not add a pair for every chapter or duplicate the pair in
the paired tracking workspace. Publish them to `textbooks/<Book>/` only with
an explicitly requested release. They are repository documentation, not
rendered or kernel-consumed textbook content.

For a new book, create both files before bulk formalization. When an existing
book gains or changes a core interface, read and update them as part of that
work. `README.md` records only the currently implemented project entrypoint,
namespace and public API. `math_collections.md` is the lightweight mathematical
manual for important concepts and intermediate nodes, including their ideal
Litex forms, representative signatures, dependencies, downstream uses, and
allowable proof holes. It is not an exhaustive inventory or status schema.

Before writing a core declaration, compare it with `math_collections.md`. If
they differ, decide whether the code or the design note is wrong; update the
design note first when the intended interface genuinely changes. Do not carry
both shapes through a wrapper, alias, compatibility predicate,
`abstract_prop`, or `trust`. Keep source declarations in source order and
update `README.md` only after the actual interface and representative use probe
verify.

## Exercise and Deferred-Proof Policy

Skip every source item explicitly labelled `Exercise` (or `Exercises`) unless
the user explicitly asks to translate it. Do not create a Litex declaration,
source-facing comment, todo entry, translation record, or coverage placeholder
for such an item: it should not appear in the translated textbook artifact.

Distinguish a standalone exercise from a definition, theorem, proposition,
lemma, corollary, or remark whose body says “leave as exercise” or otherwise
defers a proof step to an exercise. Keep that non-exercise source item visible in its original
place. Immediately before the affected Litex item, add a compact English
comment explaining that the original leaves the step as an exercise, then use
`trust` only for the corresponding unproved fact. For example:

```litex
# Source handling: the original leaves this implication as an exercise.
# Litex records the same omitted step as explicit trust.
trust $relevant_fact(...)
```

Do not call that item `checkable`; record its remaining debt as `trust` in the
paired working workspace when local bookkeeping is required.

## Strategic Policy

Use Litex builtins directly in chapter files whenever possible. The chapter
files are learning and translation artifacts first; they should show how to
write the mathematics in Litex without making the reader feel that the book
depends on a pre-existing `Analysis` or std package.

Standard-library packages are downstream products of the chapter work as much
as dependencies for it. A chapter may depend on a package only when the
dependency is doing one of two clear jobs:

1. Hiding a proof that would be too long or distracting for the chapter file.
2. Providing an axiom-like or primitive interface that the chapter intentionally
   takes as background.

Otherwise, prefer local definitions, direct Litex proof steps, or a nearby
source-facing proof-debt note over importing a package.

## Hidden Infrastructure Gate

Before treating an elementary-looking result as background, run a minimal
natural Litex probe. Do not use “obvious” or “intuitive” as a `trust` reason.
Classify the one missing interface, if any: finite enumeration or induction;
canonical construction, existence, or uniqueness; quotient, extensionality, or
invariant representation; cardinality, injection, bijection, or disjoint
decomposition; order, extrema, limits, or completeness; or algebraic closure
or normalization.

Record the source theorem, natural proof idea, exact probe failure, missing
bridge, current status, primary blocker (`trust` or `kernel_problem`), and
intended destination in the paired workspace. Preserve the source-facing
statement. Leave one-off debt at the smallest source-facing step; do not trust
an entire theorem because prose hid its infrastructure.

## Direct Or Builtin Before Citation

Write the textbook mainline first. When one exact substep is hard, record the
source proof idea, make the best small Litex attempt, and use `trust` only for
that substep. Do not stop ordinary textbook writing to redesign the kernel or
the standard library for a single blocker.

Before adding or calling a cite theorem, test the intended fact directly in the
real caller context without a wrapper theorem or `trust`. If builtin or infer
rules verify it, write the fact directly where it is used. Do not create a
`thm` merely so the chapter can cite it, and never store a trusted duplicate of
a builtin-supported fact in cite. This includes elementary set algebra,
arithmetic normalization, comparisons, and automatic type or membership facts.

Use a source-local cite package only when a substantial or library-shaped fact
remains genuinely unproved after that direct attempt and a stable named
interface is needed to keep the source mainline moving. Put it adjacent to the
source, for example `chap7_cite/main.lit`, `<source>_cite/main.lit`, or
`cite/main.lit`. Import it with the repository's module mechanism; for
repository projects, declare it with `export mod` and cite its canonical name.
Represent source-order reuse through the ordered `[export]` table rather than
inventing a statement that loads an arbitrary `.lit` path.

A cite package is an explicit proof-debt interface, not a completed std
module. Make it self-contained by importing the std modules it needs. Put
shared real source vocabulary in a small ordinary `prop`/`have` module such as
`chap9_vocab/main.lit`; do not copy chapter definitions into cite as
`abstract_prop`. Cite facts should be named `thm` or `claim` interfaces whose
only unresolved step is the narrowest `trust`, and each debt must appear in the
nearby `todo.md` or unfinished notes.

Do not move a cite theorem into `std` until its statement is stable, its proof
or intended trusted interface is understood, and multiple files genuinely need
it. Repetition alone is not enough, and a simple expected fact that fails
should be classified as missing builtin, infer, stdlib, or kernel support
instead of being hidden as citation debt.

## Interface-Scope Gate

Treat the public surface of a textbook chapter and any source-local cite or
vocabulary module as part of the mathematical exposition. A proof helper is
not a public interface merely because Litex allows it to be declared at file
scope.

Before adding a top-level `prop`, `have`, `have fn`, `template`, `claim`, or
`thm`, audit its actual consumers:

1. Keep it local when it exists only to complete one enclosing `claim` or
   `thm`. Declare the helper inside that proof body, including a local `prop`,
   a local selected value, or a local `have fn`.
2. Local recursive functions are supported. If a descending construction,
   coefficient pair, loop invariant, or measure-indexed predicate only proves
   one theorem, put its `have fn ... by induc`, projections, and induction
   invariant inside that theorem rather than exporting algorithm internals.
3. Promote a helper to chapter, vocabulary, or cite scope only when the source
   needs to name it, another chapter cites it, or at least two independent
   proofs need the same stable mathematical statement, and only after it
   passes the Direct Or Builtin Before Citation gate above. Do not promote
   speculative future reuse.
4. A public gcd-like construction should expose its definition and ordinary
   mathematical laws; names such as `candidate`, `value`, `characterization`,
   temporary coefficient projections, or a proof measure belong inside the
   proof unless they are themselves source-facing mathematics.

Use the real verifier in the enclosing scope before deciding that a helper
must be top-level. A comment saying that a declaration is “internal” is not a
substitute for lexical locality when the language can express it locally.
After a refactor, search the cite package and dependent chapters: no removed
helper name may remain as an external citation.

Use cite only for a substantial, genuinely unproved fact, not for one-off
proof scaffolding or a builtin-supported fact. Frequency does not override
this gate. A finite selection function, unique-existence construction,
induction theorem, or broad mathematical theorem is not a builtin candidate;
when broadly useful, it may be a `basics` candidate. Do not reduce reported
debt merely by moving it: track direct chapter trust separately from indirect
cite or `basics` trust.

Only use `abstract_prop` for genuinely external or still-undefined background
interfaces. If the concept is chapter vocabulary, define it as a real Litex
interface of the appropriate kind: `prop` for a relation, `have fn` for a
source-defined map or set-valued construction, and `have fn ... by exist!` for
a selected uniquely determined value.

## Builtin-First Rule

When a source reconstructs familiar mathematical objects, use Litex's builtin
interfaces when they express the intended mathematics. Preserve the source
construction as a local statement, proof sketch, or explicit debt whenever it
matters for source traceability, but do not make that construction an
unnecessary prerequisite for the chapter's checked mainline.

## Carrier-First Modeling Gate

Before writing Litex for a source definition or theorem with a nontrivial
domain, pause. First reason about the source vocabulary, search nearby
chapters and the builtin surface, and state a carrier-first modeling audit in
the task response or working record:

| Source concept | Existing Litex surface | Chosen form | Why not the nearest alternative? |
| --- | --- | --- | --- |

Do not write the Litex item until this audit selects a carrier, collection
type, remaining condition, and any reusable selected value or map.

Apply these hard rules:

1. Treat natural numbers, positive integers, integers, reals, functions, and
   finite sets as carrier/type choices first. Use the narrowest existing
   builtin or standard interface.
2. Put a collection's element domain in its type. For example, use
   `power_set(N_pos)` for a set of positive integers; do not use
   `power_set(Z)` and then add `x > 0` for every element unless no existing
   carrier can express the domain.
3. Do not restate facts that the declared type already guarantees, such as a
   set's inclusion in its ambient carrier or an element's membership in that
   ambient carrier.
4. Use `prop` only for the residual property or relation that types cannot
   express. Do not use a predicate merely to re-encode a carrier.
5. Give a minimal runnable use probe. If no suitable surface exists, report
   the exact missing type or construction as `blocked`; do not silently invent
   a broad-carrier wrapper.

Before writing the declaration, apply the `litex-definition-modeler` gate.
The carrier audit does not decide the declaration kind by itself: first decide
whether the source introduces a relation, object, function, canonical value,
or declaration family. If later code must write `f(x)`, `S(m)`, or another
application, do not encode the interface as only a `prop`. Keep a relation
such as `$divides_Z(m, x)` as a `prop` when it is the condition used inside a
set-valued function such as `mZ(m)`. Preserve the source name, domain, and
codomain, and include one application use probe before proceeding to proofs.

Read
[references/modeling-and-naming-examples.md](references/modeling-and-naming-examples.md)
when a carrier/form decision or public-interface name needs a worked bad/good
comparison.

In particular:

- Use builtin `N`, `N_pos`, `Z`, `Q`, `R`, set membership, subset, finite
  sets, `count`, tuples, Cartesian products, function equality, order,
  intervals, and induction forms when they express the intended mathematics.
- Prefer local chapter-facing theorem statements over `Module::theorem` calls
  when the proof is short and pedagogically relevant.
- If a chapter uses a std theorem to hide a long proof, add a nearby comment
  saying that the std interface was formed from this book's development, not
  that the book intrinsically depends on an external analysis library.
- Do not create source-specific wrapper predicates for concepts Litex already
  exposes naturally.
- Keep textbook coverage traceable: preserve source-facing theorem/definition
  statements in chapter order when they matter; route through std only when
  doing so hides a genuinely long proof or records an intended background
  axiom/interface.
- Treat a source's constructive developments of sets, integers, rationals, and
  reals as alternate proof routes or proof debt unless the user explicitly asks
  to formalize those constructions.
- When a construction reveals a real missing API, record it as stdlib, kernel,
  infer-rule, syntax, formulation, or diagnostics work rather than forcing the
  main chapter proof to use a lower-level encoding.

## Source-Family Guidance

- For foundational number systems, sets, tuples, functions, and finite objects,
  use builtin objects and direct proof patterns when they express the source
  statement. Keep a source construction as an alternate route or explicit debt
  rather than recreating it only to reach familiar mathematics.
- For analysis, algebra, topology, or geometry, introduce a local predicate
  only when it is genuine reusable source vocabulary. Keep theorem statements
  source-facing even when their checked proof calls a small builtin or standard
  interface.
- When a source needs a long surrounding theorem package, isolate that package
  only if it makes the main chapter more readable. Otherwise retain local
  definitions and a narrow, explicitly labelled proof debt.

## Public Interface Naming Gate

Apply this gate to every new or newly touched reusable/source-facing `prop`,
`abstract_prop`, `have`, `have fn`, and `thm`. Do not rename historical
interfaces merely to conform; migrate them only in a separate, verified change.

Before writing the declaration, state this compact audit in the task response
or working record:

| Declaration kind | Mathematical meaning | Existing or conventional candidates | Selected name | Rejected alternative and reason |
| --- | --- | --- | --- | --- |

Choose names in this order:

1. Use the usual mathematical name when one is established and the namespace
   plus type make it unambiguous, such as `min`, `sup`, `inf`, `gcd`, or
   `well_ordering_principle`.
2. Search the nearby chapter and imported public interfaces before inventing a
   synonym. Preserve one established Litex term instead of creating two names
   for the same interface.
3. When no standard name applies, use the shortest complete English name that
   states the public mathematical meaning. Name the statement, not a proof
   trick, temporary witness, implementation detail, or encoded type fact.

Use `_N`, `_Z`, `_Q`, or `_R` only when the domain distinguishes otherwise
conflicting mathematical interfaces. Omit the suffix when the conventional
name and parameter types already settle the meaning. Do not substitute verbose
`_natural`, `_integer`, or `_real` spellings merely to repeat the types.

Use one primary public name. Do not add aliases merely to keep both a canonical
and a descriptive spelling; keep source wording in nearby prose instead. A
canonical theorem name and a descriptive theorem name are both candidates in
the audit, not two interfaces to publish by default.

### Theorem Names Must State the Theorem

Include a condition in a descriptive theorem name only when it is a genuine
public hypothesis. Never expose a limitation of the current proof route as
though it were part of the mathematics. For example:

- Prefer `well_ordering_principle` when the public theorem is that every
  nonempty subset of `N` has a least element.
- Use `finite_nonempty_subset_of_N_has_least_element` only when finiteness is
  truly a stated hypothesis of the interface.
- Reject `finite_N_subset_of_positive_size_has_least`: “positive size” hides
  the ordinary mathematical condition “nonempty”, and `has_least` omits the
  object being asserted.

## Declaration Grammar

Make the declaration kind visible when no stronger standard name exists:

- Use `prop is_xxx` or `abstract_prop is_xxx` for judgments, properties, and
  relations, such as being closed, open, continuous, bounded, injective, or a
  closure of a set.
- Use `prop has_xxx` or `abstract_prop has_xxx` for existence, witness, or
  value relations, such as having a point in every epsilon neighborhood, a
  limit, a derivative, or a Riemann integral.
- Use conventional object names for functions when available; otherwise use a
  descriptive noun phrase such as `least_element_of_N_subset`, not a verb,
  `candidate`, `result`, or `_value` suffix.
- Avoid a name that restates an ambient carrier already visible in parameter
  types unless the suffix is needed to distinguish a competing interface. For
  example, keep `is_close_in_Q` when a real analogue also exists, but do not
  add `_R` to a uniquely real interface only to echo its types.

Use the topology slice in
[references/modeling-and-naming-examples.md](references/modeling-and-naming-examples.md)
as the preferred naming example when this declaration grammar is non-obvious.

## Source-Facing Comment Format

This applies to every translated textbook chapter `.lit` file. Do not write
comments that only repeat the book label. For each meaningful definition,
theorem, proposition, lemma, corollary, or remark, include a concise
explanation of the mathematics immediately before the Litex item. Standalone
source exercises are intentionally omitted under the Exercise and
Deferred-Proof Policy.

- For a definition, write the source label, then explain what the definition
  means in concrete mathematical terms. If Litex uses a builtin or a local
  interface instead of the source's construction, say so explicitly.
- For a theorem, proposition, lemma, or corollary, write what the statement is
  proving before the formal statement. Make clear what the inputs are, what the
  conclusion says, and why the result matters locally.
- For a proof, write the proof idea before the proof block. Say whether the
  proof is by unfolding a definition, proving two directions, induction,
  constructing a witness, splitting cases, chaining equalities, applying an
  order estimate, or calling a standard/local interface.
- If the checked Litex route differs from the source's proof, record both routes:
  explain the source proof idea briefly, then say which Litex/std/builtin fact
  is used for the checked proof. Put unfinished source-route details in local
  proof debt or `todo.md`.
- Keep comments useful but compact. A simple item may need two or three comment
  lines; a definition or theorem that introduces a reusable concept should get
  enough detail that a reader can understand the meaning without opening the
  book.

Example format:

```litex
# Definition 3.1.4. Equality of sets is extensional equality.
# This means two sets are equal exactly when they have the same members:
# every object belongs to the first set iff it belongs to the second set.
# In Litex proofs, use this by introducing an arbitrary element and proving
# both membership directions.
```

```litex
# Proposition 3.x.y. Subset inclusion is transitive.
# This proves that if every element of A is in B, and every element of B is in
# C, then every element of A is in C. The proof idea is to unfold subset
# membership, take an arbitrary element of A, send it through the first
# inclusion, then send the result through the second inclusion.
```

## Workflow

For a textbook workspace, first read the canonical bundled repository policy,
any source-local style guide and `todo.md`, the module documentation, and the
relevant chapter under `scripts/textbooks_drafts/<Book>/`. Keep source material,
translation records, todos, audits, and experience notes in the book's paired
`scripts/` workspace.

For long chapters, build current source with `cargo build --release`, start one
release `-session -before <current-chapter.lit>`, and submit statements from
the chapter's first one in source order as literal outermost `try:` blocks.
If current source cannot produce the release binary, report that build failure
and stop verification; do not substitute an older or debug binary. Treat clean
`-f` and whole-book `-r` runs as checkpoints or final gates, not the proof-debug
inner loop.

## Mandatory Proof-Liveness Gate

Treat a textbook proof as incomplete until it passes both checks:

1. **Backward liveness:** retain only facts that reach the theorem target, a
   required witness, an exported claim, or a source-facing calculation.
2. **Whole-chain bypass:** delete each remaining definition, reflexivity,
   membership, theorem-result, or predicate-folding chain as one candidate in
   the real chapter context. A fact waterfall may give every line a textual
   consumer while the complete path is still bypassable through a declaration,
   infer rule, or higher-level interface.

Apply a hard echo ban to automatic environment effects: `have a T` already
stores `a $in T`; declarations store their equations; case branches store their
premises; and checked witnesses, claims, and theorem calls store their results.
Do not repeat those facts solely to make the verifier's route visible.

Keep source-facing conclusions and pedagogical calculations. When a shorter
real-context probe fails, restore only the smallest exact bridge required for
`obtain`, substitution, or later inference, not the original cascade.
Dependency graphs and lexical scans may nominate candidates but cannot prove
liveness when inferred dependencies are omitted.

Review the whole touched chapter for copied proof families, definition-equation
wrappers, proof-only helpers with one consumer, long equality waterfalls, and
generated graph or audit metadata. These do not belong in the textbook artifact.
Preserve source order, source-numbered items, theorem identity, and
pedagogically decisive calculations. Do not leave an easy example as
comment-only prose: include a compact `sketch:` block or checked theorem.

1. Read the paired source workspace, the module documentation, and the
   relevant draft chapter under `scripts/textbooks_drafts/<Book>/`.
2. For a new book or a changed core interface, read or create the single
   project `README.md` and `math_collections.md`; use the latter to guide the
   important interfaces and their representative use probes.
3. Filter the source: omit standalone exercises; retain non-exercise items
   whose text defers a proof to an exercise, using the explicit `trust` comment
   policy above.
4. Understand the mathematical idea before writing Litex.
5. Choose the simplest Litex-native formulation that can support checked
   downstream analysis.
6. Preserve source traceability with labels, nearby comments, or local notes
  when the checked route differs from the source's constructional route.
7. Run the verifier for changed `.lit` files, perform the two-pass
   proof-liveness gate above, and use the exact output to make the next
   smallest correction.
8. At each core node and chapter checkpoint, compare the code with
   `math_collections.md`; repair the code or update the design note before
   continuing, then keep `README.md` aligned with the verified public API.
9. Classify each touched item as `translated`, `checkable`, or `blocked`.
10. If blocked, use exactly one primary label: `trust` or `kernel_problem`.
11. Update nearby bookkeeping: `todo.md`, unfinished notes, solved-experience
   notes, and any local JSONL/status records required by the source folder.
12. Before calling the edit complete, verify the touched fragment in the
   persistent session, run the appropriate project-aware release checkpoint,
   and record any remaining debt or blocker.

## Proof Debt

Follow the Direct Or Builtin Before Citation workflow above. Keep a one-off
blocked step as the smallest source-facing `trust`; once it is recurrent or
library-shaped, give it one named source-local cite interface only when it is
substantial and still genuinely unproved, instead of copying the trust into
each chapter. Never convert direct builtin support into citation debt. Add a
nearby source comment and a paired-workspace record saying why the step is
blocked, how the source handles it, and whether the next action is direct
proof, builtin, `basics`, or a kernel fix.

When a formerly blocked item becomes checkable, remove the stale blocker from
the paired workspace's `todo.md`, replace or delete its cite interface as
appropriate, and record the reusable lesson in that workspace's solved
experience area.

## Persistent Task Ledger

When a textbook slice, shared citation, or supporting kernel task cannot be
finished in this turn, also create or update
`todo/<YYYY-M-D>/<project>.md` at the repository root, using the current
environment date without zero padding. Track the completed source items,
remaining items/files, explicit proof-debt or kernel boundary, next smallest
action, and verifier checkpoint. This project ledger complements rather than
replaces the source workspace's todo and unfinished/experience records. Delete
it only when the scoped task is complete and verified.
