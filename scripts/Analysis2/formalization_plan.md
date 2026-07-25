# Tao Analysis II (4th ed.) Litex formalization plan

## Task context

- Task: Plan a new Litex implementation of Tao's *Analysis II*.
- Scope: The eight source chapters in `scripts/Analysis2/Analysis II.txt`,
  their mathematical interfaces, translation records, final textbook project,
  and verifier checkpoints.
- Related workspace: `scripts/Analysis2/` and the proposed
  `textbooks/Analysis2/` project.

Status: Phase 0 and the 32-item Chapter 1 vertical slice are implemented. The
ordered project runner succeeds. Chapter 1 remains proof-incomplete with 48
visible `trust` statements and two recorded selection/template
`kernel_problem`s; the next bounded milestone is proof-debt reduction before
starting the Chapter 2 slice.

## 1. Scope and source lock

The repository-local transcript is the source of truth:

- Source: Terence Tao, *Analysis II*, fourth edition.
- Local source: `scripts/Analysis2/Analysis II.txt`.
- TXT SHA-256:
  `25d4c22ebe3b74809ba0af542c3a498df0bd9e49743943bad8b112ae5867ec57`.
- Size at plan time: 13,596 lines and 429,534 bytes.

Do not silently replace this source revision. If a PDF, corrected transcript,
or later edition is introduced, first diff the numbered source inventory and
record the revision change.

The source is copyrighted. Translation records and chapter comments should use
source identifiers and concise mathematical reformulations, not reproduce long
passages. Standalone source items labelled `Exercise` or `Exercises` are
excluded completely: no Litex declaration, source-facing comment, todo entry,
or coverage placeholder is created for them. A definition, lemma, proposition,
theorem, or corollary whose proof is deferred to an exercise remains in source
order; prove it when practical, otherwise retain the statement and mark only
the omitted proof step with visible `trust`.

A validated unique-label extraction found 224 named non-exercise items. This
is the book-level coverage contract:

| Chapter | Subject | Preliminary named items |
| --- | --- | ---: |
| 1 | Metric Spaces | 32 |
| 2 | Continuous Functions on Metric Spaces | 24 |
| 3 | Uniform Convergence | 34 |
| 4 | Power Series | 38 |
| 5 | Fourier Series | 18 |
| 6 | Several Variable Differential Calculus | 26 |
| 7 | Lebesgue Measure | 28 |
| 8 | Lebesgue Integration | 24 |
| **Total** |  | **224** |

Examples, remarks, and explanatory passages are not included in the 224 count.
The manifest should retain them when they carry mathematical content, using a
formal item or a concise comment-only representation as appropriate.

## 2. Existing surfaces and the actual gap

This is not a blank-slate formalization:

- `textbooks/Analysis/` contains the current Analysis I development, including
  real sequences, limits, continuity, differentiation, and Riemann integration.
- `textbooks/Mathematics-In-Lean-Derived-Litex-Corpus/chapter11-topology.lit`
  already contains corpus-local metric-space, ball, convergence, continuity,
  compactness, completeness, and topology interfaces.
- `textbooks/Mathematics-In-Lean-Derived-Litex-Corpus/chapter13-integration-and-measure-theory.lit`
  contains corpus-local measurable-space and measure interfaces.
- `textbooks/Linear-Algebra-Done-Right/` contains reusable implementation
  experience for linear maps, finite-dimensional spaces, matrices, and norms.

These files are design evidence and sources of checked proof patterns, not
automatic dependencies of the new book. The Phase 0 probes must distinguish:

1. a builtin or stable standard interface that Analysis II should use directly;
2. an Analysis I theorem that should remain an explicit prerequisite;
3. a corpus-local interface worth adapting into the new book;
4. a stable interface that should move to `std` after multiple real consumers;
5. a genuine missing definition, theorem, inference rule, syntax feature, or
   kernel behavior.

Do not copy an existing corpus-local predicate merely because its name is
convenient. Compare its carrier, semantic role, source meaning, and downstream
use with the Analysis II concept model first.

## 3. Artifact boundary and project shape

Final reader-facing artifacts belong in one top-level module:

```text
textbooks/Analysis2/
  README.md
  math_collections.md
  litex.config
  todo.lit                         # create only when visible mathematical holes exist
  chapter01-metric-spaces.lit
  chapter02-continuous-metric-maps.lit
  chapter03-uniform-convergence.lit
  chapter04-power-series.lit
  chapter05-fourier-series.lit
  chapter06-several-variable-calculus.lit
  chapter07-lebesgue-measure.lit
  chapter08-lebesgue-integration.lit
```

Use one final `.lit` file per source chapter and export the chapters in source
order. `README.md` and `math_collections.md` are module documentation: do not
export, import, render, or pass them to the kernel. `README.md` may describe
only implemented and verified interfaces. Create `math_collections.md` from
the concept-modeler template before bulk formalization and keep the ideal
interfaces, dependency DAG, and allowable holes there.

Working artifacts stay under:

```text
scripts/Analysis2/
  Analysis II.txt
  formalization_plan.md
  todo.md
  source_manifest.yaml
  items/chapter01.yaml
  ...
  items/chapter08.yaml
  probes/
  unfinished/problem_notes/
  experience/problem_notes/
```

Each touched translation record must contain:

```yaml
source:
problem:
proof_idea:
litex_code:
comments:
```

Local records may additionally use `source_id`, `kind`, `chapter`, `status`,
and `blocker`. After an item is attempted, `status` is exactly one of
`translated`, `checkable`, or `blocked`. A blocked item has exactly one primary
blocker label: `trust` or `kernel_problem`.

Start with direct chapter proofs and narrow local `trust`. Create a
source-local cite package such as `chapter01_cite/main.lit` only after the
intended theorem has failed a direct real-caller-context probe, remains
substantial and reusable, and can be stated without copying later chapter
vocabulary. Cite debt stays explicit in `todo.md`; moving it does not reduce
the debt count.

## 4. Preliminary concept model

These are the semantic decisions the first modeling pass must test. Exact
syntax is not frozen until a minimal definition-plus-use probe verifies.

| Mathematical spine | Semantic role | Intended Litex form | Nearest rejected form |
| --- | --- | --- | --- |
| Metric-space data | Structure: carrier, distance, and laws | explicit carrier and callable distance with an `is_metric_space` law relation; test whether a small `struct` improves real callers before freezing the API | a proposition that hides the distance function and prevents `d(x,y)` |
| Metric balls, closure, interior, exterior, boundary | Set-valued constructions | `have fn` returning `power_set(X)`, with point predicates only where the source uses the judgment | a `prop` describing a candidate set without exposing the set |
| Metric convergence and candidate limit | Relation | `prop` over a displayed sequence and displayed limit | selecting a limit before uniqueness and convergence are established |
| Convergence and selected limit | Existence property plus canonical selection | `prop is_convergent`; add `have fn ... by exist!` only when later source code needs the value directly | one predicate ambiguously used both as a relation and a value |
| Cauchy, completeness, compactness, connectedness | Properties of supplied metric data or subsets | `prop` with the narrowest carrier and source quantifiers | wrappers that restate membership or ambient carrier facts |
| Continuous and uniformly continuous maps | Relations on typed callable functions | pointwise/domain `prop`s; functions remain ordinary `fn` values | a continuity object that hides the function being applied |
| Topology in optional Section 2.5 | Structure/law family on a collection of subsets | candidate open-set family plus topology laws; bundle only if field projection has real consumers | making every metric theorem depend on the optional topological abstraction |
| Function sequences and pointwise/uniform convergence | Functions plus relations | callable sequence-of-functions object and separate convergence `prop`s | encoding a function sequence as only a convergence predicate |
| Formal power series and trigonometric polynomials | Coefficient-indexed mathematical objects | callable coefficient functions and formula-defined operations | opaque existence predicates that cannot be evaluated or multiplied |
| Radius, sum, limit, Fourier coefficient | Formula-defined or canonical value | `have fn`; use unique selection when existence and uniqueness are mathematical obligations | leaving only `has_value(...)` when later chapters apply the value |
| Several-variable derivative | Candidate linear-map relation plus canonical linear map | preserve the displayed linear map; prove uniqueness before any selected derivative | copying the scalar derivative interface from Analysis I |
| Contraction, inverse, and implicit maps | Relations and selected local functions | source-facing relations plus callable selected functions after existence/uniqueness | strengthening the premise with the desired conclusion |
| Outer measure and Lebesgue measure | Callable set functions with law relations | a value carrier for nonnegative extended values, callable set functions, measurable-set relation, and measure laws | a single `is_measure` proposition with no applicable measure function |
| Lebesgue integral | Candidate-value relation plus selected value | simple-function construction, nonnegative integral, integrability relation, then selected integral | selecting an integral before measurability, existence, and uniqueness |
| Product measure and Fubini | Construction plus reusable results | callable product construction and named source theorems | treating Fubini as automatic infrastructure or hiding it in `trust` |

For every core interface, the detailed model must record ordinary meaning,
semantic role, Litex form, source anchor, immediate use probe, dependencies,
and the exact allowable proof/existence/uniqueness/well-definedness hole.

## 5. Typed dependency DAG

Edge legend:

- `import`: explicit dependency on Analysis I, a builtin, or a stable package;
- `signature`: carrier, domain, or codomain dependency;
- `definition`: the definition unfolds to the prerequisite;
- `well_definedness`: an application or selected value needs the prerequisite;
- `existence`, `uniqueness`, `selection`: canonical-construction stages;
- `proof`: theorem dependency;
- `trust/source`: explicit source omission or temporary proof boundary.

```text
Litex builtin carriers and set/function surfaces
  --import--> Analysis II foundations
Analysis I real limits, derivatives, and Riemann integration
  --import--> Analysis II foundations

carrier X + distance d
  --signature/law--> metric-space interface
metric-space interface
  --definition--> balls, interior/exterior/boundary, closure, open/closed sets
metric-space interface + sequences
  --definition--> convergence, subsequence, Cauchy sequence
candidate metric limit
  --proof/uniqueness--> metric limit uniqueness
Cauchy convergence
  --definition--> completeness
subsequence convergence
  --definition--> compactness

metric topology + typed functions
  --definition--> continuity and uniform continuity
compactness + continuity
  --proof--> extrema, uniform continuity, connected-image theorems

function sequences + metric/real limits
  --definition--> pointwise and uniform convergence
uniform convergence + continuity/integration/differentiation
  --proof--> Chapter 3 preservation theorems
uniform convergence + coefficient sequences
  --definition/proof--> power series and analytic functions
power-series algebra
  --proof--> exponential, logarithm, complex, and trigonometric interfaces
trigonometric functions + periodic functions
  --definition--> Fourier coefficients, convolution, Fourier series

finite-dimensional linear maps + metric continuity
  --signature--> several-variable derivative relation
derivative existence + uniqueness
  --selection--> derivative linear map
completeness + contraction
  --proof--> contraction mapping theorem
derivative + contraction
  --proof--> inverse and implicit function theorems

sets + countable families + extended nonnegative values
  --definition--> outer measure
outer measure
  --definition/proof--> measurable sets and Lebesgue measure
measurable sets + preimages
  --definition--> measurable functions
measurable simple functions
  --definition--> simple integral
simple approximation
  --existence/well_definedness--> nonnegative measurable integral
positive/negative parts
  --definition--> absolutely integrable functions and integral
product measure + iterated integrals
  --proof--> Fubini theorem
```

The main anticipated source-order deviation is local: uniqueness must precede
each `have fn ... by exist!` selection even when the source introduces the
notation earlier. Section 2.5 is optional and must not become a prerequisite
for earlier metric-space results. The measure/integration spine may be modeled
while earlier proof debt remains, but final files and source-facing items stay
in the book's chapter order.

## 6. Execution phases

### Phase 0 — Source manifest, module model, and foundation probes

1. Create `source_manifest.yaml` and manually validate all 224 preliminary
   named items, source order, item kinds, and proof-deferred-to-exercise cases.
2. Add mathematically substantive examples and remarks without importing any
   standalone exercise.
3. Create `textbooks/Analysis2/litex.config`, `README.md`, and
   `math_collections.md`. Keep `README.md` minimal until code verifies.
4. Probe the real dependency mechanism for Analysis I. Do not copy Analysis I
   declarations or invent aliases if a canonical import or stable interface
   exists.
5. Run definition-plus-use probes for metric data, balls, convergence,
   subsequences, closure, Cauchy sequences, completeness, and compactness.
6. Compare the probes with the existing topology corpus. Adopt only interfaces
   whose carriers, semantic roles, and source uses match.
7. Freeze the Chapter 1 concept DAG only after the use probes verify or produce
   exact recorded blockers.

### Phase 1 — Chapter 1 vertical slice (32 named items)

Implement the complete source-ordered Chapter 1, which is the required
20--50-item vertical slice:

1. metric-space laws and the principal concrete metrics;
2. convergence and uniqueness of metric limits;
3. balls, interior, exterior, boundary, closure, open and closed sets;
4. relative topology;
5. subsequences, limit points, Cauchy sequences, and completeness;
6. compactness, boundedness, Heine--Borel, nested compact sets, and the
   sequential compactness consequences retained by the source.

This milestone is complete only when all 32 items have structured records,
every retained interface has an immediate use probe, every proof boundary is
small and visible, no exercise has leaked into the artifacts, and the Chapter
1 runner result contains no JSON error.

### Phase 2 — Chapters 2 and 3

Build continuous maps on metric spaces, product-space continuity, compact and
connected images, the optional topology interface, pointwise and uniform
convergence, the uniform metric, function series, the Weierstrass M-test, and
preservation of continuity, integration, and differentiation. Keep pointwise
and uniform convergence as distinct relations and test every preservation
theorem against the exact source hypotheses.

### Phase 3 — Chapters 4 and 5

Build formal power-series operations, convergence radii, analytic functions,
Abel's theorem, multiplication, exponential/logarithm, complex and
trigonometric functions, then periodic functions, inner products,
trigonometric polynomials, periodic convolution, Fourier coefficients, and
the Fourier/Plancherel theorems. Do not let arithmetic normalization stand in
for finite-sum, convergence, or rearrangement arguments.

### Phase 4 — Chapter 6

Model linear transformations and derivatives in several variables, then
partial/directional derivatives, chain rules, second derivatives, the
contraction mapping theorem, and inverse/implicit function theorems. Reuse
stable linear-algebra interfaces only after caller-context probes; do not make
the chapter depend on an unrelated textbook namespace merely for naming
convenience.

### Phase 5 — Chapters 7 and 8

Model the extended nonnegative value carrier, outer measure, failure of naive
additivity, measurable sets and functions, simple functions, nonnegative
integration, absolute integrability, comparison with the Riemann integral,
product measures, iterated integration, and Fubini. Treat countable unions,
countable sums, monotone limits, measurability, and well-definedness as visible
dependencies rather than one broad measure-theory axiom.

### Phase 6 — Debt reduction and publication audit

1. Prove local pedagogical facts directly before creating cite interfaces.
2. Promote only stable, multiply used interfaces to `std`; record kernel work
   only for an actual verifier/runtime defect.
3. Apply backward proof liveness and whole-chain bypass checks to every
   completed theorem.
4. Generate definition and fact graphs and compare them with the planned DAG.
5. Reconcile the manifest, chapter records, `todo.md`, `todo.lit`, experience
   notes, module documentation, and actual verifier state.

## 7. Per-item translation loop

For every retained source item:

1. Read the surrounding source and write the natural-language mathematical
   idea before Litex code.
2. Run the carrier-first, semantic-role, declaration-form, and naming audits.
3. Record `source`, a concise `problem` reformulation, `proof_idea`,
   `litex_code`, and `comments`.
4. Write the source-facing English comment immediately before the final Litex
   declaration.
5. Test the natural definition and immediate caller use in the real module
   context.
6. Write the smallest proof and use exact verifier output to make the next
   smallest correction.
7. Try direct builtin/inference support before a wrapper theorem, cite, or
   `trust`.
8. If still blocked, keep the best partial proof, trust only the exact missing
   fact, add the required nearby reason comment, and create an unfinished note
   with the exact failure and next action.
9. Classify the result as `translated`, `checkable`, or `blocked`, with primary
   blocker `trust` or `kernel_problem`.
10. When a blocker becomes checkable, write the solved-experience note first,
    then remove the stale todo and unfinished note.

## 8. Verification gates

Use the persistent Litex process and literal `try:` blocks as the proof-debug
inner loop. A full chapter or project run is a checkpoint.

For a noninteractive changed-file checkpoint:

```bash
target/release/litex -compact -f textbooks/Analysis2/chapter01-metric-spaces.lit
```

For the ordered project checkpoint:

```bash
target/release/litex -compact -r textbooks/Analysis2
```

Inspect the verifier result for `"result": "error"`; shell exit status alone
is not a verification result. At chapter milestones, generate definition and fact
graphs in `/private/tmp` and compare actual public dependencies with
`math_collections.md`. Use strict verification as the zero-trust gate, not as a
reason to hide first-pass proof debt.

## 9. Completion criteria

The book is complete only when:

- all eight chapter files exist and run in source order;
- the manually validated source manifest has no missing, duplicated, merged,
  or reordered retained item;
- all 224 validated named items have a structured record
  and reader-facing formal or explicitly blocked representation;
- substantive examples and remarks are represented while every standalone
  exercise remains absent;
- objects, functions, selected values, relations, structures, and theorems
  retain their correct semantic roles;
- every remaining `trust` is the smallest source-facing step, appears in the
  mathematical and technical ledgers where required, and has a concrete next
  action;
- no one-use proof helper remains public when lexical locality suffices;
- project output contains no JSON `result:error`;
- `README.md` describes only verified public behavior and
  `math_collections.md` matches the final interface DAG; and
- `textbooks/Analysis2/` contains only publishable `.lit` files,
  `litex.config`, `README.md`, and `math_collections.md`, while working records
  remain under `scripts/Analysis2/`.

## 10. Next bounded handoff

Begin only Phase 0 and the Chapter 1 slice:

1. validate the 32 Chapter 1 labels and source-deferred proofs;
2. create the project configuration and the two module documents;
3. write the Chapter 1 concept inventory and typed DAG;
4. verify the eight foundational definition-plus-use probes;
5. then implement Chapter 1 in source order.

Do not begin Chapter 2 until the Chapter 1 carriers, callable constructions,
use probes, item records, and runner checkpoint agree.
