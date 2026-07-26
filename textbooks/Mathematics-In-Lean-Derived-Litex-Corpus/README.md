# Litex translation pressure-test corpus

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

## Begin with one checked fact

Chapter 2 contains this small example:

~~~litex
forall a, b R:
    (a + b) * (a + b) = a * a + 2 * (a * b) + b * b
~~~

Litex checks the identity by polynomial normalization. No chapter-local
`trust` is used for this fact. The example illustrates the interface being
tested: write the mathematical fact directly and let the checker account for
routine consequences. It does not, by itself, establish a comparison with
Lean or a Lean-kernel certificate.

Chapter 2's reusable algebra core is now carried by checked
`AdditiveCommutativeGroup<s>`, `Group<s>`, and flat `Ring<s>` values. A ring
exposes `add`, `zero`, `neg`, `mul`, and `one` directly, while its structure
body composes the reusable additive-group law predicate. Chapter 8 reuses that
canonical `Ring`, keeps its stronger two-sided group experiment under the
distinct name `TwoSidedGroup`, and gives `Module` direct scalar and vector
operations. Chapters 7, 9, 10, and 12 continue the same flat-data rule for
commutative rings, Euclidean domains, fields, vector spaces, and real normed
spaces. Chapter 3 uses refined order-relation carriers; Chapters 11 and 13 use
refined filter, metric, topology, and measurable-space carriers. Lower-level
operation-plus-law signatures are explicitly named `*_from_laws`.

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

The corpus deliberately omits exercises, repeated tactic demonstrations, and
Lean elaboration examples that do not introduce a new retained mathematical
interface. Consequently it should not be used to learn Lean, to measure
Mathlib coverage, or to compare source-line counts between the two systems.

## Evidence and limits

The declaration-level source registry was regenerated on 2026-07-26 from the
pinned non-solution Lean files. It replaces the older grouped workflow counts
as the source-coverage surface.

| Status | Count | Meaning |
| --- | ---: | --- |
| Source declarations | 1096 | Individually enumerated non-solution Lean declarations. |
| Checkable correspondences | 143 | A matching checked Litex route is recorded. |
| Translated/excluded rows | 4 | Standalone exercises excluded by the corpus policy. |
| Blocked or unaligned rows | 949 | No declaration-level checked correspondence is currently established. |
| Executable trust directives | 2 | The two C11 continuity-equivalence directions contain narrow proof debt. |

The former 291/202/89 table remains historical workflow bookkeeping and is not
reported as source coverage. Current counts are generated in
`scripts/mathematics_in_litex/source_item_coverage.md` from
`source_registry.jsonl`.

At the Litex source-module level, this project has no configured `std` import
and no cite module. The small shared number-theory layer is ordinary checked
Litex in the source-ordered chapters: Chapter 2 defines divisibility and gcd,
Chapter 4 defines primality, and Chapter 5 selects the Euclidean integer
quotient from a checked unique-existence fact. This is a precise claim about
module dependencies, not a claim that the corpus needs no verifier support.
Arithmetic normalization, finite-set operations and extrema, and the narrow
Euclidean-quotient existence rule remain kernel builtin boundaries.

The declaration-level counts and blocker labels are in
[`scripts/mathematics_in_litex/source_item_coverage.md`](../../scripts/mathematics_in_litex/source_item_coverage.md)
and [`blocker_taxonomy.md`](../../scripts/mathematics_in_litex/blocker_taxonomy.md).

Strict project success would establish that the configured no-`std` graph
loads and verifies every exported chapter in order. The current draft does not
pass that gate because strict mode correctly rejects its two localized Chapter
11 continuity-equivalence `trust` statements.

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

The current Litex-to-Lean bridge supports only a limited trust-free arithmetic
subset. This thirteen-chapter project is not currently compiled to Lean.
Within the supported subset, trusted or unsupported forms must not be
presented as trust-free Lean output. See
[`docs/Litex_and_Lean.md`](../../docs/Litex_and_Lean.md) for the current
implementation boundary.

## Run entrypoint

From the `golitex` repository root:

~~~sh
RUST_MIN_STACK=8388608 target/release/litex -compact -r scripts/textbooks_drafts/Mathematics-In-Lean-Derived-Litex-Corpus
~~~

The full project acceptance gate is:

~~~sh
RUST_MIN_STACK=8388608 target/release/litex -compact -strict -r scripts/textbooks_drafts/Mathematics-In-Lean-Derived-Litex-Corpus
~~~

At the current checkpoint this command fails at
`chapter11-topology.lit:676`: strict mode rejects the first user `trust` in
`continuous_iff_open_preimages_forward`. A second localized `trust` remains in
the reverse direction at line 684. The ordinary release module gate and the
registered Chapter 13 `-f` prefix checkpoint succeed, but the draft must not be
called strict-checkable until both debts are removed.

The project exports only `chap1` through `chap13` in source order. It has no
`[import std]` section and no cite export. Cross-chapter objects, functions,
predicates, and theorems use explicit module qualification.

## Corpus map

- `chap1`–`chap5`: introductory functions and facts; basic algebra and logic;
  sets/functions; and elementary number theory.
- `chap6`: finite counting, list/tree/formula interfaces, checked list
  induction consequences, and the callable Boolean valuation update.
- `chap7`–`chap9`: records, indexed-simplex midpoint, Gaussian integers,
  checked integer ring and natural-scalar objects, inherited submonoids,
  groups, rings, ideals, polynomials, square expansion, and integer units.
- `chap10`: vector spaces, linear maps, subspaces and quotients, eigen data,
  matrices, bases, and dimension.
- `chap11`: filters, metric spaces, topological spaces, compactness, filter
  limit composition, eventuality laws, continuous composition, the forward
  pairwise-to-anchored Cauchy bridge, and complete-space convergence. The
  source coinduced-topology composition equivalence remains deferred.
- `chap12`: elementary and normed-space differential calculus.
- `chap13`: analytic epsilon vocabulary, measurable spaces and their closure
  laws, generic countably additive measure candidates, and almost-everywhere
  relations. ENNReal and integration theory are deferred in `todo.lit`.

`math_collections.md` records the cross-chapter mathematical interfaces. The
source manifest, status ledgers, extraction tools, and unfinished notes live
in `scripts/mathematics_in_litex/` so that working artifacts remain outside
the final module.

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
[CC BY 4.0][cc-by]. This corpus changes the selection, language, naming, proof
organization, and implementation of the source material: it retains
definitions and main results, omits exercises and repeated Lean presentations,
and translates the retained mathematical content into independently
maintained Litex files. The names “Mathematics in Lean”, “Lean”, and “Mathlib”
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
