# Litex Showcases

These collections offer several ways into Litex: follow a mathematical argument,
read a chapter development, study a problem's proof, or see how checked
mathematics connects to other tools. Choose a collection by what you want to
learn; analysis, algebra and geometry are subjects within these categories.

For a short mathematical introduction, begin with [Linear Algebra in Litex](linear_algebra/README.md).
For a systematic introduction
to writing proofs, follow [The Mechanics of Litex Proof](The-Mechanics-of-Litex-Proof/README.md).

## Mathematical lecture notes

A lecture develops a small mathematical world: definitions lead to examples,
lemmas and a few central theorems. Inspiration from a book does not make a
lecture a chapter-by-chapter adaptation.

| Collection | Mathematical progression | Scope |
| --- | --- | --- |
| [Linear Algebra in Litex](linear_algebra/README.md) | Coordinate operations → vector spaces and subspaces → span, bases and unique coordinates | Selected lectures inspired by Axler's *Linear Algebra Done Right*, using the real plane. |
| [Topology in Litex](topology/README.md) | Open and closed sets → continuous maps → homeomorphisms | Two chapters with discrete and indiscrete two-point spaces, continuous composition and the closed-preimage criterion. |
| [Abstract Algebra in Litex](abstract_algebra/README.md) | Groups and subgroups → homomorphisms → kernels and injectivity | Two chapters on group theory, using integer addition, multiples, doubling and the zero map. |
| [Mathematical Concepts in Litex](math_concepts_in_litex/README.md) | Subject-specific slices from elementary constructions to undergraduate structures | A collection of checked vertical slices, rather than a complete curriculum. |

## Textbook adaptations

These developments follow a source's chapter structure. Their coverage maps
identify the mathematics included, selected examples and omitted material.

| Collection | Source and direction | Scope |
| --- | --- | --- |
| [Tao's Analysis I in Litex](analysis/README.md) | Terence Tao's *Analysis I*: induction, sets and maps, real numbers, limits, series and countability | A non-strict adaptation of selected Chapters 2–8 and Appendix A. It retains four user axioms and one abstract predicate, and is not a complete formalization. |

## Litex proof tutorials

Here the learning path concerns proof writing itself: how to introduce objects,
use definitions, supply witnesses and carry established facts into later arguments.

| Collection | Learning path | Scope |
| --- | --- | --- |
| [The Mechanics of Litex Proof](The-Mechanics-of-Litex-Proof/README.md) | Calculations and definitions → constructions → functions, sets and relations → induction and arithmetic | A teaching module with checked citations and Chapters 0–10. See its README for the lesson map and checking boundary. |

## Problems and solutions

Each problem provides a concrete destination for the mathematics. Read its
hypotheses and proof idea alongside the formal statement, including any chosen
coordinate or scalar model.

| Collection | Problems | Scope |
| --- | --- | --- |
| [IMO inequalities](imo_inequalities/README.md) | Polynomial and radical inequalities, equality cases and optimal constants | Five official problems with five standalone proofs. |
| [IMO geometry](2D_Geometry/README.md#imo-examples) | Triangle and circle configurations, constructions, inequalities and incidence counting | Twelve problems with fifteen solution packages. The README distinguishes full configurations from scalar and normalized variants. |

## Mathematical theory libraries

A theory library supplies reusable vocabulary and theorems. Its reader may
need a definition or lemma for another proof rather than a prescribed lesson sequence.

| Collection | Mathematical interface | Scope |
| --- | --- | --- |
| [Plane geometry library](2D_Geometry/README.md#library-entrypoints) | Coordinate pairs, vectors, dot products and determinants → lines, circles and triangle lemmas | Definitions-only and complete-library entrypoints. The same collection also contains the separately listed IMO solutions. |

## Features and applications

These examples use mathematics to explain a particular Litex capability and
show how its output can be used elsewhere.

| Collection | Demonstrated capability | Scope |
| --- | --- | --- |
| [Litex proofs in ordinary Lean](litex_to_lean_adapter/README.md) | Litex source → generated Lean proof → handwritten adapter → ordinary Lean/Mathlib theorem | Worked interoperability examples, including a nonzero-denominator identity and a fractional linear involution; not a general proof-length comparison. |
| [Write Mathematically Correct Code with Litex](Write_Mathematically_Correct_Code_With_Litex/README.md) | One mathematical definition used in proofs and exported as Python or C | A concrete Newton-step calculation with an exact-real residual bound. Target floating-point rounding, overflow and surrounding application correctness are outside the demonstrated guarantee. |

## Reading scope and verification

The categories describe each collection's purpose, not its completion or
verification status. Each collection's own README and available verification
records specify its assumptions, supported scope and dated checks. A selected
chapter development is not a completed book. Litex checks still rely on its
verifier and builtin mathematical rules.

New showcases should join the category matching their main reading purpose.
Describe their mathematical subject, reading scale and implemented scope in
the entry. A collection serving two purposes can have two entrances, as the
geometry collection does here.
