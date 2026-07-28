---
name: litex-proof-writer
description: Write, translate, repair, simplify, and classify Litex mathematical proofs and dataset items. Use when Codex needs to create or fix .lit files, translate MATH500, miniF2F, high-school, GSM8K, Math23K, Mechanics, textbook, or theorem statements into Litex, derive a nonredundant natural-language proof spine before formalization, prevent checkable proofs from reimplementing existing mathematical interfaces, run Litex verifier feedback loops with persistent REPL plus literal try blocks, reduce trust proof debt, or classify Litex blockers.
---

# Litex Proof Writer

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
  outermost `try:` block per theorem, definition, or small proof fragment. A
  successful block commits to the session; immediately write the accepted
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

## Workflow

1. Write the shortest honest proof spine in ordinary mathematical language
   before editing Litex.
2. Find the existing definitions, theorems, templates, and local proof patterns
   that implement those mathematical moves.
3. Write the smallest runnable Litex proof whose blocks correspond to the
   proof spine.
4. Run the verifier and read the exact output.
5. Make the next smallest correction without changing the proof's abstraction
   level merely to satisfy the verifier.
6. After it verifies, run the mandatory proof-liveness audit and remove
   inference echoes, dead facts, and bypassable derivation chains.
7. Classify the result as `translated`, `checkable`, or `blocked`.

Before creating or repairing a reusable definition, apply the
`litex-definition-modeler` gate. State the semantic role, choose the Litex
form, preserve the source name/domain/codomain, and write one minimal use
probe before spending time on downstream proof steps. A source-defined
function or set-valued construction must remain `have fn` even when its body
contains a predicate. A `prop` may describe the relation used by that body,
but it is not a substitute for the returned function or object.

For a new top-level module, or when adding or changing a core reusable
interface, read its single `README.md` and `math_collections.md` before writing
substantial code. `README.md` is the current implemented API; the second file
is the mathematical manual for important concepts and ideal interface shapes.
Use one pair for the whole module, not one per file or submodule. Compare the
candidate declaration with that manual: repair the code when it drifted, or
update the manual first when the mathematical design genuinely changed. Do not
keep incompatible forms through wrappers, aliases, `abstract_prop`, or
`trust`. After the use probe verifies, update `README.md` with the actual API.

## Nonredundant Proof Spine Gate

Before writing Litex, state the proof as the fewest meaningful mathematical
moves a competent reader would normally use. Name the existing interface that
justifies each move. Prefer the highest established abstraction: use an
inverse-function theorem, decomposition lemma, induction principle, or
structure law instead of rebuilding its construction locally.

During formalization, require every nontrivial code block to correspond to one
proof-spine move or to one verified Litex bridge that the verifier genuinely
needs. If a two-step mathematical argument grows into a local function,
existence proof, uniqueness proof, and helper claim, stop before accepting the
code merely because it runs. Search for the missing reusable interface and
classify the expansion as one of:

- failure to reuse an existing definition, theorem, or template;
- a missing general mathematical interface;
- an exact parser, verifier, well-definedness, or elaboration bridge; or
- mathematics that really is constructive at this level.

The block count and shape must remain visibly aligned with that spine. A
two-step proof must not turn into a line-by-line log of associativity,
commutativity, identity, and rewriting states. Put the decisive calculation in
one equality chain. If the verifier cannot rewrite an inner argument through an
outer function, add only the smallest explicit congruence or inner-rewrite fact
shown necessary by a failed shorter real-context run.

After the proof verifies, compare its blocks against the original proof spine.
Delete or replace any block that only re-proves a packaged fact, reconstructs
an existing object, or exposes implementation detail absent from the
mathematical argument. Re-run the shortened proof in its real context after
each deletion. Keep extra code only when the shorter form actually fails, and
record the exact reason; do not normalize a repeated local workaround as good
proof style.

Write the proof spine in the working analysis or item metadata. Put it into the
`.lit` source only when it is a useful mathematical comment, not as a narration
of obvious syntax. See `references/proof-style.md` for the bijection/inverse
example and the final alignment audit.

Do not leave an easy textbook or dataset example as comment-only prose. At
minimum, use a `sketch:` block to state and formalize the example's actual
objects and claims; when the facts are directly checkable, prefer a checked
theorem or a fully verified sketch. Prose may explain the example but cannot
replace its formal mathematical content.

## Clean Interface and Local-Proof Gate

Use lexical proof scope as the default boundary for proof-only machinery. Do
not create a file-level declaration simply because it makes the next lines
shorter.

Before adding a top-level `prop`, `have`, `have fn`, `template`, `claim`, or
`thm`, identify every real consumer in the current source tree:

- If the helper serves exactly one proof procedure, declare it inside that
  enclosing `claim` or `thm`. This applies to temporary predicates, witness
  relations, finite-set bounds, uniqueness criteria, recursive coefficient
  pairs, projections, and induction invariants.
- A local `have fn` may be recursive (`by induc` / `by strong_induc`). Prefer
  that form for an algorithm used only to prove one theorem, then expose only
  the theorem's mathematical conclusion.
- Promote a helper only when it is a source-facing definition, a stable cited
  theorem, or has verified use in two or more independent proofs. “It may be
  useful later” is not evidence for a public API.

For example, a Bézout theorem may define its recursive Euclidean coefficient
pair, its projections, and its measure invariant inside the theorem, while
the outside interface remains only the existential Bézout conclusion. Likewise
an implementation predicate saying that a candidate is greatest should not be
published when ordinary divisibility and algorithm theorems are the intended
reader-facing laws.

Run the candidate in its real enclosing scope. If local declaration is blocked
by an actual parser or verifier limitation, record the smallest reproduction;
do not broaden the interface merely as an untested workaround. After cleanup,
search dependent files and remove every citation of the localized helper.

For any newly created or touched dataset, textbook, contest, exam, Mechanics,
or generated-math item, follow the Translation Item Contract in
`references/dataset-translation.md`. Do not submit raw Litex code without the
source, problem, proof idea, Litex code, and concise comments when relevant.

## Mainline-First Refinement

For textbook, dataset, or long theorem-family work, prefer a mainline-first
refinement workflow over trying to write a perfect top-to-bottom proof in one
pass. First make the important mathematical spine readable and runnable. Then
isolate substantial or library-shaped supporting facts that remain genuinely
unproved as named local interfaces that can be proved later.

### Cite Eligibility Gate

Treat a cite package as a namespace for genuine, unresolved proof debt. It is
not a place to give names to facts that the verifier already proves through
builtin or infer rules.

Before adding any cite theorem, test its intended statement directly in the
real caller context, without a wrapper theorem or `trust`:

1. If the direct fact verifies, use that fact directly. Do not create a `thm`
   only so callers can write `by thm`, and never put a trusted copy in a cite
   package. Builtin provenance is already the proof source.
2. Repetition alone does not make a fact cite-worthy. Elementary set algebra,
   arithmetic normalization, comparison, type/membership consequences, and
   other builtin-supported facts stay direct even when many files use them.
3. A cite candidate must remain genuinely unproved after one direct real-context
   attempt, have a substantial or library-shaped proof that would distract
   from the mainline, and need a stable named interface while that proof is
   deferred. Record the exact missing proof and future discharge path.
4. If a simple expected fact does not verify, classify the missing builtin,
   infer, stdlib, or kernel support instead of hiding the gap in cite.

For example, do not put a trusted `set_commutativity` theorem in cite merely
to expose commutativity of `intersect` and `union`. When those equalities are
builtin-checkable, write the equalities directly at the use site. If the
source itself numbers such a theorem, keep that source-facing theorem in its
source location and let its body verify directly; it is still not citation
proof debt.

Use this pattern when a supporting fact is mathematically clear but would
distract from the current source item:

1. Keep the main `.lit` file focused on source-facing definitions, theorem
   statements, key proof route, and checked local derivations.
2. Put repeated real vocabulary in a small `*_vocab/main.lit` module using
   ordinary `prop`/`have` definitions. Do not copy real definitions into a cite
   file with `abstract_prop`.
3. Put genuinely unproved, lengthy supporting facts in a source-local cite
   package such as `chap7_cite/main.lit`, `<source>_cite/main.lit`, or
   `cite/main.lit`.
   Cite facts should be named `thm` or `claim` interfaces, with unresolved
   proof steps marked by narrow `trust` proof debt. Never add a cite wrapper
   for a fact already discharged by builtin or infer rules.
4. Import cite packages with `import`, not `run_file`. Reserve `run_file` for
   source-order reuse where expanding the earlier file is intentional.
5. Make cite theorem statements reusable and abstract enough for the local
   mathematics, not one-off facts tailored to a single proof line.
6. Consider a reusable project package only after the fact is fully checkable,
   has a stable interface used by at least three independent source families,
   and remains explicitly declared through `litex.config`. Do not create or
   restore an automatically loaded mathematical `std`.

This is the default collaboration pattern for large formalization: build the
important structure first, keep proof debt explicit and named, then refine the
surrounding facts one at a time.

## Turn Scaffolding Into Checked Proofs

The goal is not only to make files run. Existing files may use `trust` or
`abstract_prop` as temporary scaffolding so a larger translation remains
runnable while the missing mathematics stays visible.

For a newly encountered obligation, write the natural proof spine and make one
direct real-context Litex attempt. If that attempt identifies a proof, library,
inference, syntax, or formulation blocker, immediately preserve the intended
statement, put `trust` only on the blocked substep, record the exact debt, and
continue. Do not spend further proof-search iterations unless the user
explicitly asks to remove that trust.

When the task explicitly targets existing debt, improve it by proving an
existing `trust`, replacing a broad trust with a checked outline plus one
narrow trust, turning a clear `abstract_prop` into a real definition, or
factoring repeated debt into one stable reusable interface. Test any cite
candidate directly first; builtin-supported facts never become trusted cite
wrappers.

Keep status honest: `checkable` only after the relevant code verifies without
`trust`; `translated` when the statement has a natural Litex form; `blocked`
when the obstacle is understood and recorded with primary label `trust` or
`kernel_problem`.

## Reference Corpus

Before writing or repairing nontrivial Litex, search the bundled corpus copied from this repository's `docs/` and `examples/` trees. Start with `references/litex-corpus/INDEX.md`, then use targeted `rg` searches under `references/litex-corpus/docs` and `references/litex-corpus/examples`. Do not load the whole corpus into context; read only the matching snippets or files needed for the current proof.

Use the corpus this way:

- Prefer `docs/Manual.md` for syntax and verifier behavior.
- Prefer `examples/01_proof_patterns/README.md` for proof idioms.
- Prefer runnable `.lit` files under `examples/` when choosing a checkable proof shape.
- Treat `_internal/scratch` examples as useful experiments, not polished public style.

## Verification Loop

For repeated proof iteration, build current source with `cargo build --release`
and start one persistent
`target/release/litex -compact -session -before <current-file.lit>` process.
Use an older binary only when the current source cannot produce the release
binary; never use the debug binary for performance-sensitive verification.
Submit the target's statements from the first one in source order, with each
candidate protected by a literal outermost `try:`. This is the default inner
loop because failed attempts normally roll back only themselves and do not
replay the already-loaded project prefix.

Do not use Python-side `sandbox_run()` as the primary workflow when direct
Litex `try:` is available. Do not rerun a release `-f long_file.lit` target
after every small edit; use it only for file checkpoints and final file
verification. Use `-trust-before-line` only for the disk-first preview
described in the critical verifier contract above, and use `-r` only for an
explicit complete-module gate.

Keep one statement or small proof fragment per outer `try:`. After success,
write that accepted source to disk without the wrapper and submit the next
source statement. After failure, repair and resubmit only that fragment in the
same process.

## Mandatory Proof-Liveness Audit

Treat proof-trace redundancy as a failed completion criterion even when the
file verifies. Write the mathematical proof, not a log of verifier states.
Classify and remove all five forms:

- **Result or context echo:** restates a `by thm` conclusion only to mirror the
  current goal, or repeats an existential before `obtain`, an obtained body,
  case premise, binder-derived type fact, witness body, definition equation,
  reflexivity, or builtin/infer consequence.
- **Wrapper echo:** uses an empty or one-line `claim` for a fact that should be
  written directly, or wraps proved definition clauses in an atomic prop goal
  and then repeats the folded target.
- **Equality or comparison waterfall:** prints every rewrite state and then
  repeats an endpoint equality/inequality already supplied by the chain.
- **Representation drift:** creates alpha-equivalent lambdas, aliases, or other
  local variants and then adds pointwise/extensional transport to reconcile them.
- **Dead or bypassable chain:** has no live mathematical consumer, or its local
  links consume one another even though an earlier declaration, infer rule, or
  established interface reaches the endpoint without the whole chain.

Run two passes after every new or touched proof verifies:

1. Work backward from the final target, witnesses, and exported claim results;
   remove facts with no live consumer.
2. Inspect every remaining multi-line bridge for a bypass. Delete the whole
   candidate chain in a literal `try:` block in the real enclosing context.
   If deletion fails, restore only the smallest exact bridge demonstrated by
   the failure, not the original cascade.

Apply a hard echo ban after declarations, binders, `obtain`, witnesses, and
cases. Use stored conclusions directly and do not republish obtained or case
facts. After proving a concrete prop's instantiated clauses, finish with bodyless
`by def $P(args)` from the inside out; do not force builtin, abstract, or
theorem-supplied facts through `by def`.

Review an immediate explicit result after `by thm` separately. Keep at most one
when it selects one conclusion of a multi-result theorem, instantiates a generic
result at the source-facing object under discussion, or bridges into the
predicate or representation consumed next. A source-facing aggregation may
display several distinct returned results. Delete a pure current-goal
restatement with no such reader-facing transition.

Reuse one canonical function expression or named helper throughout a proof.
Do not introduce extensionality merely to reconcile binder renaming or an
equivalent lambda spelling created locally. Keep an implied line only when a
real-context deletion probe proves that it is the smallest necessary bridge or
a source-facing mathematical move. Dependency graphs and lexical scans may
nominate candidates, but cannot prove liveness because they may omit inferred
facts. See `references/proof-style.md` for the full cascade test and examples.

## Catastrophic Bloat Gate

Treat the following recurring shapes as stop-ship proof bloat, not harmless
verbosity:

- **Definition-equation facade:** a `have fn` definition is followed by public
  zero/successor/evaluation theorems that merely restate its stored equations,
  and callers then cite those wrappers instead of using the definition.
- **Expanded micro-pattern:** a routine move such as choosing a midpoint,
  turning two-sided bounds into an absolute-value bound, preserving order at a
  limit, shifting a finite prefix, or using an involution is rederived as a
  long local trace instead of using one existing mathematical interface.
- **Mirror-copy proof:** lower/upper, positive/negative, forward/reverse, or
  limsup/liminf arguments duplicate the same case tree or algebra with signs
  reversed instead of sharing the genuine common lemma.
- **Proof-only public sprawl:** one-consumer aliases, witness packagers,
  evaluation lemmas, or induction machinery become top-level API. Keep them
  local, use the underlying interface directly, or delete them; promote only a
  source-facing item or a helper with at least two independent consumers.
- **Premise and interface tax:** a theorem carries parameters or hypotheses
  unused by both its mathematical proof and conclusion. Remove genuinely
  redundant premises rather than making every caller manufacture them.
- **Recursive proof log:** finite enumeration, running maxima, dyadic blocks,
  or recursive constructions print every index-range, type, reflexive, and
  constructor consequence. State the invariant once and retain only the base,
  recursive mathematical move, and final use.
- **Non-mathematical source cargo:** generated metadata, audit counters,
  verifier-debug history, or a source-free language tutorial lives inside a
  mathematical proof file. Move machine data to an artifact and design notes
  to documentation; keep the proof source reader-facing.

Before accepting a touched file, inspect every `claim` with at most three body
lines, every run of at least five equality/comparison lines, every new or
touched helper with fewer than two independent consumers, and every theorem
premise not referenced in its proof or conclusion. Also compare repeated
lambdas and mirrored proof families for representation drift or copy-paste.
These are mandatory review triggers, not automatic deletion rules. Probe the
whole candidate path in the real enclosing `try:` context, keep source-facing
calculations, and restore only the smallest bridge that failure evidence shows
is necessary. Never apply a broad regex deletion to equality or comparison
lines.

## Quantified Redundancy Audit

For a chapter- or book-wide cleanup, classify code before estimating savings:

- `source_required`: source-facing definitions, results, examples, identities,
  and source order;
- `interface_required`: stable declarations with real downstream consumers;
- `proof_spine`: mathematical cases, induction invariants, witnesses, and
  decisive theorem applications;
- `reader_bridge`: an explicit theorem result that selects, instantiates, or
  translates the fact a reader needs for the next mathematical move;
- `verifier_bridge`: the smallest type, well-definedness, representation, or
  rewrite fact whose necessity was demonstrated by a failed shorter proof;
- `verified_removable`: a removed echo, wrapper, dead chain, or redundant
  endpoint whose real-context replacement verifies; and
- `blocked_by_existing_debt` or `unknown`: candidates that have not been
  honestly tested.

Count declaration consumers and fact-graph successors only to rank candidates.
Zero later consumers does not make a source theorem removable, and a locally
consumed chain can still be bypassable. Report a structural floor separately
from the current-verifier practical floor, and label all projected savings as
estimates until deletion probes pass. Keep generated counts and dependency
metadata outside mathematical `.lit` source.

## Proof Style

- Before adding a proof-body line, ask whether the current target already
  follows from the facts the preceding statement stored. Use a literal `try:`
  block to test the shorter version in the real local context.
- Omit verifier echoes when they add no mathematical move: do not restate a
  goal after a successful `by contra`; do not manually fold a witness's
  existential body back into its enclosing `prop`; and do not restate `Q(x)`
  after `P(x)` when a known implication or iff already derives `Q(x)`.
- Prefer the minimal witness form when the substituted existential body is the
  whole proof obligation. For example, write
  `witness exist u, v Z st {1 = a * u + b * v} from x, y` without a `:` block;
  Litex automatically checks `1 = a * x + b * y`. Add a witness body only for
  genuine intermediate reasoning, a nontrivial bridge, or a pedagogical step.
- Keep the source-facing theorem statement and pedagogically meaningful
  calculations. Compress repeated proof-body facts, not the mathematical claim
  a reader is meant to see.
- Keep comments mathematical. Do not narrate verifier states, code-generation
  decisions, cleanup history, local debugging, or audit counts in proof source.
- Do not delete a bridge merely because it is mathematically implied. In
  particular, conjunctions may need explicit component facts for `obtain`, a
  named package fact may be needed by a later substitution chain, and a
  function-definition equality may seed inference even when direct equality
  checking can unfold the function. Verify every proposed deletion in the
  surrounding proof, not only in a toy snippet.
- When several formulations are possible, use the most Litex-native and
  simplest checkable formulation as the main proof. Treat source-text shape or
  lower-level raw Litex expression shape as secondary unless the user asks for
  that comparison.
- When defining mathematical vocabulary, use names that stay close to standard
  mathematical wording. Do not simplify a conventional term into a private
  shorthand, and do not invent a new phrase when the usual one is clear.
- Name predicates by how they read in ordinary mathematics. Use `prop is_xxx`
  or `abstract_prop is_xxx` for judgment/property predicates, and use
  `prop has_xxx` or `abstract_prop has_xxx` when the declaration is a relation
  about existence, a witness, a candidate value, or a package. If the source
  introduces the value/function itself and later code must apply or cite it,
  use `have`, `have fn`, or `have fn ... by exist!`; do not hide that interface
  behind a `has_xxx(..., value)` predicate.
- Avoid suffixes such as `_R` or `_Q` when the parameter types already say the
  domain. If a distinction is genuinely needed, spell it out in the name, such
  as `is_close_in_Q` or `has_limit_in_R`. Avoid `_value` in predicate names;
  write `has_riemann_integral(I, f, s)` rather than
  `riemann_integral_value_R(I, f, value)`.
- Keep an explicit intermediate fact only when it is a mathematical move or
  the smallest verified bridge; checkability alone is not a reason to write it.
  Prefer one readable equality chain over a waterfall of one-step facts.
- Prefer direct universal facts over redundant `claim: prove:` scaffolding
  when the `forall` statement already expresses the intended semantic fact.
  For example, write:

```litex
forall a, b R, x oc(a, b):
    x $in R
    a < x
    x <= b
```

  instead of:

```litex
claim:
    prove:
        forall a, b R, x oc(a, b):
            x $in R
            a < x
            x <= b
    x $in R
    a < x
    x <= b
```

  Use `claim:` only when the current proof needs to introduce a concrete
  local consequence that is not already being stated directly, or when a
  sub-proof is genuinely needed to export a final fact into the surrounding
  context.
- For cancellation or applying the same algebraic context to both sides, prefer one equality/order chain over separate intermediate facts. Add a named theorem only when the pattern is reused non-locally.
- For algebraic/numeric failures, split large jumps into smaller equalities before looking for new rules.
- For zero-product reasoning, use explicit division steps.
- Do not use `trust` to hide ordinary proof obligations. When a blocker
  requires `trust`, keep it on the narrowest substep, document it, and keep the
  rest explicit.
- Keep runnable snippets self-contained.
- For ordinary `forall` facts, do not write an empty `=>:` body.

Example naming pattern:

```litex
prop has_point_in_epsilon_neighborhood(X set, x R, epsilon R_pos):
    X $subset R
    exist y X st {y $in R, abs(x - y) < epsilon}

prop is_adherent_point(X set, x R):
    X $subset R
    forall epsilon R_pos:
        $has_point_in_epsilon_neighborhood(X, x, epsilon)

prop is_closure_of(C, X set):
    C $subset R
    X $subset R
    forall x C:
        $is_adherent_point(X, x)
    forall x R:
        $is_adherent_point(X, x)
        =>:
            x $in C

prop is_closed_subset(X set):
    $is_closure_of(X, X)

prop is_epsilon_neighborhood_inside(X set, x R, epsilon R_pos):
    forall y R:
        abs(x - y) < epsilon
        =>:
            y $in X

prop is_open_subset(X set):
    X $subset R
    forall x X:
        exist epsilon R_pos st {$is_epsilon_neighborhood_inside(X, x, epsilon)}

prop is_sequence_in_subset(a seq(R), X set):
    X $subset R
    forall n N_pos:
        a(n) $in X
```

## Blockers

When an item cannot be completed, record the smallest reproduction and choose exactly one primary label:

`trust` or `kernel_problem`.

Before writing a blocker, classify the root cause more precisely. This
root-cause class is human-facing metadata; it does not replace the primary
Litex label above.

1. `direct_definition`: the missing piece should be a `prop is_xxx` /
   `prop has_xxx` / `abstract_prop is_xxx` / `abstract_prop has_xxx`
   definition, not a theorem proof.
2. `general_theorem_interface`: the local step is an instance of a reusable
   theorem family. Prefer adding or recording the general `thm` interface over
   solving only one occurrence.
3. `skipped_by_previous_pass`: a previous translation skipped a harder item, but
   no verifier evidence says it is blocked. Try one direct real-context Litex
   formulation before recording debt.
4. `true_proof_debt`: the concepts and interfaces are clear, but the proof is
   genuinely long or not yet formalized.
5. `litex_blocker`: verifier, kernel, parser, syntax, or diagnostics blocked a
   natural statement. Use `kernel_problem` only when the issue appears to be in
   core verifier/runtime/proof-model behavior; otherwise keep `trust` and
   describe the surprising behavior.
6. `naming_or_structure`: the issue is namespace, theorem naming, file
   organization, or chapter/source traceability, not missing mathematics.
7. `background_axiom`: the item is a main trusted interface that should be
   introduced with `trust` temporarily as std/background, with its trusted role
   documented.
8. `repeated_local_interface`: several local proofs need the same small
   interface. Abstract it into a lemma or prop instead of copying the local
   workaround.

For abstractions, distinguish two kinds:

- Mathematical abstraction: factor the common structure of a family of objects
  or theorems, such as groups, metric spaces, finite sets, or derivatives.
- Litex-expression abstraction: add a notation, object shape, statement form, or
  helper interface that makes many propositions easy to write, even if the
  underlying mathematics is not more general.

For source work under `scripts/` or a local translation workspace, update the nearby `todo.md` with concise blocker notes. Remove completed blocker notes when they no longer block the work.

## References

- Read `references/litex-corpus/INDEX.md` when searching bundled Manual/docs/examples.
- Read `references/proof-style.md` for common Litex proof moves.
- Read `references/litex-repl-try-workflow.md` when running iterative verification.
- Read `references/dataset-translation.md` when translating benchmark or dataset items.

## Persistent Task Ledger

When a proof, textbook slice, dataset batch, or needed kernel follow-up cannot
be completed in this turn, create or update
`todo/<YYYY-M-D>/<project>.md` at the repository root, using the current
environment date without zero padding. Record the current verified prefix,
the exact remaining theorem/proof step or minimal repro, its status and
blocker boundary, the next smallest action, and the verifier command. This
ledger complements the source's own todo, unfinished, and experience records;
delete it only when the scoped task is complete and verified.
