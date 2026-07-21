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

## What this corpus is for

- **Translation research.** It tests whether source mathematical interfaces
  remain natural when written as Litex objects, functions, properties, and
  facts.
- **Gap discovery.** A failed or trusted translation identifies proof debt,
  a library gap, or a missing language/kernel capability.
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

The current item ledger was last audited on 2026-07-21. Chapters 1–6 have
completed the move away from executable chapter-local proof debt; Chapters
7–13 have not yet been migrated.

| Status | Count | Meaning |
| --- | ---: | --- |
| Checked records | 194 | The retained Litex item has a checked local proof or construction route. |
| Trusted records | 117 | The legacy executable interface remains in an as-yet-unmigrated Chapter 7–13 file. |
| Blocked records | 48 | The source mathematics is not claimed in executable code and is recorded in comment-only `todo.lit`. |
| Total records | 359 | Definitions, main results, and necessary construction helpers retained from the source snapshot. |
| Executable `trust` directives | 296 | Literal trust boundaries remaining in the unchanged Chapter 7–13 files. Chapters 1–6 contain none. |

The detailed chapter counts and blocker labels are in
[`scripts/mathematics_in_litex/coverage.md`](../../scripts/mathematics_in_litex/coverage.md)
and [`blocker_taxonomy.md`](../../scripts/mathematics_in_litex/blocker_taxonomy.md).

A successful project run means that every executable declaration is
well-formed. It does **not** mean that all 359 records have been proved.
Unimplemented mathematics in migrated Chapters 1–6 is absent from executable
code and listed honestly in the comment-only `todo.lit`; legacy executable
debt remains in Chapters 7–13 until those chapters receive the same treatment.

The current Litex-to-Lean bridge supports only a limited trust-free arithmetic
subset. This thirteen-chapter project is not currently compiled to Lean.
Within the supported subset, trusted or unsupported forms must not be
presented as trust-free Lean output. See
[`docs/Litex_and_Lean.md`](../../docs/Litex_and_Lean.md) for the current
implementation boundary.

## Run entrypoint

From the `golitex` repository root:

~~~sh
RUST_MIN_STACK=8388608 target/debug/litex -runner -r textbooks/Mathematics-In-Lean-Derived-Litex-Corpus -compact
~~~

The project imports `std/basics` and exports `citation`, then `chap1` through
`chap13` in source order. Cross-chapter objects, functions, predicates, and
theorems use explicit module qualification.

## Corpus map

- `chap1`–`chap5`: introductory functions and facts; basic algebra and logic;
  sets/functions; and elementary number theory.
- `chap6`: finite counting, list/tree/formula interfaces, and their
  source-facing induction results.
- `chap7`–`chap9`: records and Gaussian integers; algebraic hierarchies and
  quotients; then groups, rings, ideals, and polynomials.
- `chap10`: vector spaces, linear maps, subspaces and quotients, eigen data,
  matrices, bases, and dimension.
- `chap11`: filters, metric spaces, topological spaces, compactness, and
  sequential results.
- `chap12`: elementary and normed-space differential calculus.
- `chap13`: interval integration, measurable spaces and measures, Bochner
  integration, Fubini, convolution, and change of variables.

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
- In migrated chapters, unfinished source mathematics is omitted from
  executable code and recorded in the comment-only `todo.lit`; it is never
  counted as a proof. Chapters 7–13 still use the older typed-`trust` policy
  while their migration is pending.

Any remaining executable trust belongs to the smallest source-facing proof or
construction currently missing. It must not weaken a function into a
proposition, turn a closed fact into a wrapper predicate, or hide a quotient
compatibility condition. These rules are modeling safeguards, not evidence
that the missing mathematics has already been proved.

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
