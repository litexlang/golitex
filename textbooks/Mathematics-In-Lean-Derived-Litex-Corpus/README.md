# Litex translation pressure-test corpus

> **Development status:** This module is developed in public and may contain
> work at different maturity levels. Its presence in the repository is not a
> completion claim; the verification evidence, explicit `trust` boundaries,
> and known limitations below describe what is currently established.

This independently maintained Litex corpus uses selected mathematical
definitions, results, and constructions from *Mathematics in Lean* as test
inputs. Its purpose is to learn where Litex's readable, fact-oriented
interface works naturally, where it needs better library or kernel support,
and which verified fragments can eventually be exported to Lean.

This is **not** an alternative edition of *Mathematics in Lean*, a port of its
Lean pedagogy, or a claim to reproduce the capabilities of Lean or Mathlib.
The project is not affiliated with or endorsed by the book's authors, the
Lean project, Mathlib, or the Lean community. Readers who want to learn Lean
should use the excellent [official interactive book][mil-book] and its
[upstream repository][mil-repo].

The 2026-08-05 native-writing audit updated the corpus to use current Litex
interfaces where earlier translations had remained at a lower level. Binary
set operations use `intersect`, `union`, and `set_minus`; restricted images
use `fn_range` and `have by preimage`; generic function properties use native
`injective`, `surjective`, and `bijective`; measurable-set consumers bind the
refined `MeasurableSpace` carrier; and the finite-sum and tail-Fibonacci
functions use checked `have fn ... by induc` recursion. These migrations
lowered the executable trust count from 224 to 210. The full acceptance and
the deliberate non-migrations are recorded in
[`experience/problem_notes/2026-8-5-litex-native-writing-audit.md`](../experience/problem_notes/2026-8-5-litex-native-writing-audit.md).

## Begin with one checked fact

The retained complete structure-oriented Chapter 2 contains this small
example:

~~~litex
forall a, b R:
    (a + b) * (a + b) = a * a + 2 * (a * b) + b * b
~~~

Litex checks the identity by polynomial normalization. No chapter-local
`trust` is used for this fact. The example illustrates the interface being
tested: write the mathematical fact directly and let the checker account for
routine consequences. It does not, by itself, establish a comparison with
Lean or a Lean-kernel certificate.

The default [`chapter02-basics.lit`](chapter02-basics.lit), exported as
`chap2`, is setting-first. Named environments such as
`AdditiveCommutativeGroupSetting`, `GroupSetting`, and `RingSetting` make the
ambient operations the theorem subjects, so their bodies say `mul(a, zero)`
rather than `ring.mul(a, ring.zero)`. A setting is an elaboration-time bundle
of theorem parameters and laws, not a runtime mathematical value.

An independent structure-oriented presentation lives in
[`textbook2/chapter02-basics-struct.lit`](textbook2/chapter02-basics-struct.lit),
exported there as `chap2_struct`. It owns the checked
`AdditiveCommutativeGroup<s>`, `Group<s>`,
flat `Ring<s>`, one-field `PartialOrder<s>` and `MetricSpace<s>`, and
`Lattice<s>` values, together with their construction laws and residual
properties. These objects remain the right interface when a theorem packages,
compares, or transports whole mathematical systems. The two Chapter 2 files
do not cite or import one another and each verifies in isolation.

The publication module exports `./textbook2` as `MILAlternative` because Chapters
3, 5, and 7--12 retain existing first-class structure APIs. Their references
are therefore explicit, for example
`MILAlternative::chap2_struct::Group<G>`. This module-level dependency is not
used by `chapter02-basics.lit`.

At a deliberate struct-to-setting call boundary, the struct view must be
visible. For example,
`chap2::add_neg_cancel(A, unfold &MILAlternative::chap2_struct::AdditiveCommutativeGroup<A>{group}, a)`
spreads `add`, `zero`, and `neg` in declaration order. Struct parameters and
law clauses are not spread. The independent-proof design, proof journal, and
final gates are recorded in
[`chapter02-settings-default-acceptance.md`](../experience/problem_notes/chapter02-settings-default-acceptance.md).

## What this corpus is for

- **Translation research.** It tests whether source mathematical interfaces
  remain natural when written as Litex objects, functions, properties, and
  facts.
- **Gap discovery.** A failed translation identifies missing mathematics,
  a library gap, or a possible language/kernel capability gap.
- **Compiler input.** Small trust-free fragments can serve as future
  Litex-to-Lean conformance cases.
- **Constructive comparison.** The useful question is not which system is
  better, but which proof-interface choices are visible in a particular
  mathematical example.

The current completion target keeps source exercises and admitted declarations
in scope. Repeated tactic demonstrations may share one checked mathematical
counterpart, but a source `sorry` is never treated as an exclusion.
Consequently this corpus should not be used to learn Lean or to compare raw
source-line counts between the two systems.

## Evidence and limits

All 14 main-module exports plus the separately configured one-file
`MILAlternative` module passed the release repository gates with semantic
`ok=true` on 2026-08-06. The two Chapter 2 presentations also passed isolated
file gates. Chapters
3–13 contain
localized `trust` debt. Chapter 4 retains four
template computation equations for Schröder–Bernstein. Chapters 5 and 6 retain
the explicit inductive/recursive, multiplicity, counting, and structural-proof
interfaces completed in the current low-dependency translation wave. Chapter
7 retains permutation-record extensionality and Gaussian ring/Euclidean-domain
proofs. Chapter 8 retains generic scalar recursion, module/product law
packages, and quotient well-definedness/monoid laws. Chapters 9 and 10 expose
the resumed algebra and linear-algebra interfaces; their free/presented,
finite-group, quotient, polynomial, matrix, basis, and finite-dimensional
proofs retain localized trust debt. Chapter 11 has no executable `trust` or
`axiom`: its filter, compactness, Baire, compact-subsequence, and finite-
subcover theorem bodies check. Closed-unit-interval compactness, compact
continuous extrema, and dense continuous extension remain explicit
non-executable proof goals, so zero trust is not presented as proof of those
three source claims.
Chapters 12 and 13 additionally expose the basic norm and continuous-linear-map
examples, callable operator norm, the real-scalar Banach–Steinhaus statement
and checked proof assembly, selected Fréchet derivative, and the AE/eventually
interface, whose definitional equivalence is checked; their remaining
construction and proof boundaries are explicit. The Banach–Steinhaus assembly
uses the checked Chapter 11 closed-cover Baire theorem but still depends on
localized trusted closed-level-set, completeness-transport, recentering, and
shell interfaces.
These boundaries retain
source-facing callable objects instead of substituting proposition wrappers;
declarations depending on them are translated, not checkable.

Completion is tracked by original book section and named mathematical family.
The former declaration registry was retired because its one-to-one matching
treated collapsed examples and existing but unregistered Litex interfaces as
untranslated. It must not be used as a mathematical completion percentage.
The current section inventory and work order are maintained in
[`scripts/mathematics_in_litex/PLAN.md`](../../mathematics_in_litex/PLAN.md).

At the Litex source-module level, this project has no configured `std` import
and no cite module. The small shared number-theory layer is ordinary checked
Litex in the source-ordered chapters: Chapter 2 defines divisibility and gcd,
Chapter 4 defines primality, and Chapter 5 selects the Euclidean integer
quotient from a checked unique-existence fact. This is a precise claim about
module dependencies, not a claim that the corpus needs no verifier support.
Arithmetic normalization, finite-set operations and extrema, and the narrow
Euclidean-quotient existence rule remain kernel builtin boundaries.

Strict project success establishes that the configured no-`std` graph loads
and verifies every exported chapter in order. The continuity equivalence now
uses refined topology carriers and checked neighborhood/open-preimage proofs.

The same pressure test found a verifier issue in automatic universal-fact
matching across unrelated free set parameters. It was fixed on 2026-07-22:
only parameters bound by the matched universal fact may now be instantiated,
while captured outer parameters remain rigid. The C11 proofs retain their
explicit projection theorems as readable interfaces, and the former semantic
counterexample is now a rejecting kernel regression.

Two former completeness gaps are now closed. Nested anonymous functions are
matched up to alpha-equivalence without confusing captured variables, and
carrier-dependent template applications unfold when their carrier arguments
remain symbolic. The strict C10 template reproduction and the nested-function
lookup reproduction both pass on 2026-07-23. Some C10-C13 theorems retain
definition-expanded lambdas or set builders because those forms expose the
pointwise mathematics directly, not because named template unfolding is still
blocked.

The current Chapter 9 polynomial surface has checked finite-support
constructions for `polynomial_X`, `polynomial_C`, pointwise `polynomial_add`,
finite Cauchy-convolution multiplication, recursive power, finite evaluation,
and the displayed `X - r` root theorem. Natural degree is executable; its
conditional multiplication law remains a localized trust boundary. Chapter 10
has a checked coordinatewise product vector space, checked pairing and
copairing linearity, a checked singleton-supported `direct_sum_single`, checked
finite-sum matrix multiplication, and a checked identity matrix. The universal
direct-sum lift, quotient structures, determinant and inverse constructions,
and basis selections remain visibly trusted.

The current Litex-to-Lean bridge supports only a limited trust-free arithmetic
subset. This thirteen-chapter project is not currently compiled to Lean.
Within the supported subset, trusted or unsupported forms must not be
presented as trust-free Lean output. See
[`src/to_lean/README.md`](../../../src/to_lean/README.md) for the current
implementation boundary.

## Run entrypoint

From the `golitex` repository root:

~~~sh
RUST_MIN_STACK=8388608 target/release/litex -compact -runner -r scripts/mathematics_in_litex/textbook
~~~

The full project strict gate is:

~~~sh
RUST_MIN_STACK=8388608 target/release/litex -compact -strict -runner -r scripts/mathematics_in_litex/textbook
~~~

This release gate passed on 2026-07-28 before the current localized trust
boundaries were introduced. It is expected to reject the current Chapter 4–8
trust debts until they are discharged; the ordinary project runner remains
the current executable checkpoint.

The project exports only `chap1` through `chap13` in source order. It has no
`[import std]` section and no cite export. Cross-chapter objects, functions,
predicates, and theorems use explicit module qualification.

## Corpus map

- `chap1`–`chap5`: introductory functions and facts; basic algebra and logic;
  uniqueness of real sequence limits;
  sets/functions, including a checked callable choice-with-default inverse and
  typed binary and indexed image/preimage operations and laws, its
  injective/left-inverse and surjective/right-inverse characterizations,
  plus the complete callable Schröder–Bernstein construction and bijection
  theorem relative to the four explicit computation-equation trusts; and
  elementary number theory.
- `chap6`: finite counting, callable list operations, independent binary-tree
  and propositional-formula carriers with recursive interfaces, and the
  callable Boolean valuation update.
- `chap7`–`chap9`: records, indexed-simplex midpoint, a callable permutation
  group, Gaussian commutative-ring and Euclidean-domain objects, checked
  integer ring and natural-scalar objects, callable self/integer modules,
  inherited submonoids, a callable fraction quotient monoid, groups, rings,
  ideals, callable free/presented and quotient groups, finite-group and action
  statements, callable unit structures, checked representative-independent
  quotient-ring operations and commutative-ring laws, CRT maps,
  polynomials, square expansion, and integer units.
- `chap10`: vector spaces; linear maps with checked zero preservation,
  pointwise addition, scalar multiplication, scalar endomorphisms, and
  composition; typed endomorphism composition and subtraction of a scalar
  endomorphism; checked image, preimage, kernel, and range subspace closure;
  checked intersection, top, and bottom subspaces; the map/comap subset
  adjunction; checked span closure and its full subset adjunction; quotients;
  a typed and surjective canonical quotient projection; injective-kernel and
  surjective-range characterizations; eigen data together with the checked
  typed eigenspace/kernel identity for `phi - a • id`; matrices; bases; and
  dimension; callable linear-equivalence inverses, binary and indexed product
  and direct-sum interfaces, inherited-subspace and quotient structures,
  internal decompositions and quotient lifts, polynomial evaluation on
  endomorphisms, minimal/characteristic polynomials, Cayley–Hamilton, general
  matrices, coordinates, change of basis, and selected finite bases.
- `chap11`: filters, metric spaces, topological spaces, compactness, filter
  limit composition, eventuality laws, continuous composition, the forward
  and reverse Cauchy bridges, complete-space and geometric-step convergence,
  promoted principal/map/comap filters, real-limit algebra, compact uniform
  continuity and extrema, continuous distance and quadratic composition,
  closed-limit and compact interval/closedness interfaces, the Baire statement, induced/coinduced topology
  interfaces and comparison, changed-topology continuity, homogeneous product
  topology, separation and neighborhood bases, dense extension, sequential
  closure, cluster points, filter compactness, convergent subsequences,
  mapped cluster points, compact images, and finite indexed subcovers. The
  chapter has zero executable trust/axiom declarations. Three foundational
  source claims remain explicitly unproved goals: real closed-unit-interval
  compactness, compact continuous extrema, and dense continuous extension.
- `chap12`: relational and selected real derivatives, explicit sine and pi
  background, sum and power examples, local extrema, Rolle, mean value,
  real normed spaces and named norm laws, callable continuous linear maps and
  operator norm, pointwise and uniformly bounded operator families, the
  real-scalar Banach–Steinhaus theorem with its Baire/shell proof spine,
  asymptotic relations, and selected Fréchet-derivative interfaces.
  `RealNormedSpaceSetting` and `RealNormedSpacesSetting` abbreviate the repeated
  one-space and source/target ambient binders without changing theorem
  signatures.
  Elementary selected-derivative and analysis-library proofs remain localized
  trust debt.

Recursive positive-prop projection now checks norm nonnegativity, the norm
triangle inequality, and the additivity and scalar-compatibility projections
of continuous real-linear maps directly from their existing law packages.
Sound projection from grouped universal conclusions also checks scalar norm
compatibility. Classical implication packaging checks the zero-norm iff
wrapper directly from its two norm-law directions.
- `chap13`: measurable spaces and generic countably additive set functions,
  almost-everywhere truth and its eventuality interface,
  callable oriented and whole-line real integrals, logarithm and reciprocal
  background, both fundamental theorems, and callable real convolution.
  Integral construction and theorem proofs remain localized trust debt.

`math_collections.md` records the cross-chapter mathematical interfaces. The
single section-based plan, concrete development blockers, and solved problem
notes live in `scripts/mathematics_in_litex/` so that working artifacts remain
outside the final module.

## Modeling and trust boundary

- `prop` names a reusable candidate property or relation.
- `have`, `have fn`, and `template` introduce an object, callable
  construction, or carrier-dependent construction.
- A closed source assertion is written directly as a fact or a named `thm`.
- When Litex cannot express a source equivalence as one top-level theorem
  result, the corpus records its forward and reverse facts separately.
- Unfinished source mathematics is omitted from executable code and recorded
  in the comment-only `todo.lit`; it is never counted as a proof.
- No standard-library theorem or cite theorem is silently supplying the local
  number-theory proofs; their reusable definitions and lemmas are visible in
  the source chapters. Kernel builtin and verifier behavior remains a separate
  implementation boundary.
- A checked generic interface is not presented as a missing specialization.
  For example, Chapter 13 implements a parameterized countably additive
  measure law while leaving the ENNReal construction and ENNReal-valued
  theorems explicitly deferred.

These rules are modeling safeguards, not evidence that the omitted mathematics
has already been proved. The welcoming way to read the corpus is: executable
chapters show what Litex currently checks; `todo.lit` says plainly what remains.

## Source, credit, and modifications

We are grateful to Jeremy Avigad, Patrick Massot, the contributors to
*Mathematics in Lean*, and the wider Lean and Mathlib communities for making a
carefully organized public resource available. The source snapshot used for
this corpus is commit
`6dfa2c166a410d2f0f278d327ea81ae0fa6d3c32` of the upstream user repository.

The upstream repository publishes its code under the
[Apache License 2.0][mil-license], and the online book identifies its text as
[CC BY 4.0][cc-by]. This corpus changes the language, naming, proof
organization, and implementation of the source material. It retains exercises
and admitted declarations as proof targets, while repeated Lean presentations
may share one mathematical implementation. The names “Mathematics in Lean”,
“Lean”, and “Mathlib”
are used only to identify provenance and technical context.

## Feedback is welcome

Corrections are especially welcome when this corpus misstates a source
definition, overlooks a required hypothesis, describes Lean or Mathlib
unfairly, hides an indirect trust dependency, or claims more than the recorded
evidence supports. Such reports help both the translation corpus and the
Litex-to-Lean bridge become more precise.

[mil-book]: https://leanprover-community.github.io/mathematics_in_lean/
[mil-repo]: https://github.com/leanprover-community/mathematics_in_lean
[mil-license]: https://github.com/leanprover-community/mathematics_in_lean/blob/master/LICENSE
[cc-by]: https://creativecommons.org/licenses/by/4.0/
