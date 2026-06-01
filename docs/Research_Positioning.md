# Research Positioning

Jiachen Shen and The Litex Team, 2026-05-21. Email: litexlang@outlook.com

Markdown source: https://github.com/litexlang/golitex/blob/main/docs/Research_Positioning.md


## Thesis

Litex explores a fact-oriented interface for ordinary mathematical reasoning.
The user states mathematical facts, and the verifier grows an explainable
checked context by checking well-definedness, builtin rules, known facts, and
known universal facts.

Litex is intentionally narrower than Lean, Coq, or Isabelle. It does not
compete on library depth, foundational generality, or production maturity. Its
research question is different:

> Can a proof language reduce proof-engine bookkeeping for textbook-style
> mathematics by making facts, context growth, and verifier feedback the main
> interface?

## Non-Goals and Boundary

Litex should not be presented as a replacement for mature proof assistants, a
production verification platform, or a system whose current examples settle
large foundational questions. The project is a pressure test for one interface
hypothesis:

> Litex is not trying to replace Lean. It tests a different hypothesis: that a
> smaller, readable, fact-oriented formal language can make checked mathematics
> cheap enough for students, domain scientists, and AI agents to produce useful
> formal data at scale.

The main risks should be stated directly in research-facing material:

- the trusted base is larger than a small proof kernel;
- builtin and infer rules need clear mathematical specifications and tests;
- `know` introduces assumptions or proof debt, not checked consequences;
- current examples and benchmark slices are prototype evidence, not production
  certification;
- AI-generated Litex proof attempts still need verifier output, assumption
  tracking, and human or automated audit.

## Why Accept a Larger Trusted Base

Litex intentionally shifts more ordinary mathematical structure into the
checker. The surface language is relation-first: users write facts about
objects, sets, functions, domains, equality, order, and predicates, and the
checker tries to grow the context from those facts.

This is different from a design where the user first navigates a large hierarchy
of abstractions, typeclass instances, library lemmas, and proof commands. Litex
instead makes many common mathematical relationships available as builtin or
inferred background. The trade-off is explicit:

- the trusted implementation becomes larger;
- builtin and inferred steps require documentation and tests;
- the user-facing proof language becomes smaller, more direct, and closer to
  textbook reasoning;
- the feedback loop becomes more convenient for students, applied users, and AI
  agents that need to repair local derivations.

This is not a claim that a larger trusted base is better in general. It is the
specific prototype choice that makes the Litex interface worth testing.

## Design Point

Most Litex scripts are sequences of proof actions over mathematical facts:
introduce an object, state a fact, prove a local claim, name witnesses from an
existential, split cases, or record a reusable universal fact.

The checker tries to make common mathematical structure directly usable:

- equality chains;
- membership and subset reasoning;
- arithmetic and order facts;
- finite set and tuple facts;
- function-domain and function-value facts;
- existential witnesses;
- universal statements matched by shape.

This makes the proof script look closer to a textbook argument. The user often
states the next mathematical fact directly instead of choosing a tactic or
library lemma that packages the same move.

Another design point is that a development can start at the abstraction level
where the mathematics naturally lives. Litex does not force every topic to begin
with a concrete encoding. A file can introduce domains with `have`, primitive
relations with `abstract_prop`, derived relations with `prop`, and axioms or
background facts with `know`. This lets users state the intended structure first
and add concrete models or lower-level constructions later.

The clearest current example is the
[Hilbert Axioms of Euclidean Geometry](https://litexlang.com/doc/Tutorial/Example_Hilbert_Axioms_of_Euclidean_Geometry)
tutorial. It treats points, lines, planes, incidence, betweenness, and
congruence as an abstract relational interface. Litex checks how those relations
are used and reused; it does not require Euclidean geometry to be reduced to
coordinates before the development can begin.

## Relation to Mature Proof Assistants

Lean, Coq, and Isabelle are mature systems with deep foundations, substantial
automation, large libraries, and expert communities. Litex should not be
presented as a replacement for them.

Litex explores another point in the design space:

- set-theoretic surface rather than a type-theoretic programming surface;
- facts and statements rather than proof terms as the main user interface;
- context growth rather than tactic-state navigation as the primary proof
  metaphor;
- builtin ordinary mathematics rather than user-visible reconstruction of every
  basic concept.

This design is less general. The possible benefit is lower interaction cost for
ordinary textbook mathematics and clearer local feedback for proof repair.

For a detailed comparison with Lean, see
[Litex vs Lean](https://litexlang.com/doc/Litex_vs_Lean).

## Research Questions

Litex is useful if it helps answer concrete questions:

1. Does fact-oriented proof writing reduce bookkeeping in textbook
   formalization?
2. Which mathematical concepts should be primitive at the surface, and which
   should be library-defined?
3. How large can builtin mathematical background become before it hurts
   trust, debugging, or portability?
4. Can verifier output explain accepted facts well enough for users to audit
   proof steps?
5. Does local fact-level feedback make proof repair more effective than
   lower-level proof states?
6. Can Litex serve as a preformal or intermediate layer for systems with deeper
   foundations and larger libraries?

## Best Current Evidence

The strongest evidence is The Mechanics of Litex Proof as a full runnable
development, not a single showcase theorem. It translates a sequence of
textbook-style proof examples into Litex and shows the intended interaction:
write mathematical facts, run the checker, inspect the local explanation, and
continue growing the context.

That corpus matters because it exercises many proof shapes at once:
calculation, logic, induction, functions, tuples, sets, relations, existential
witnesses, reusable universal facts, and longer proof repair.

MATH500 and MiniF2F-style tasks are the next pressure tests. They are useful
even when they fail, because each failure can be classified as a language,
standard-library, builtin-rule, infer-rule, formulation, or diagnostic gap.

For abstract mathematics specifically, the best current demo is the
[Hilbert geometry tutorial](https://litexlang.com/doc/Tutorial/Example_Hilbert_Axioms_of_Euclidean_Geometry).
It shows how Litex can work with primitive relations and Hilbert-style axioms
without requiring a coordinate model first.

## What to Evaluate

For proof assistant researchers, the most useful feedback is not whether Litex
is already mature. It is not.

The useful questions are:

- Is the soundness boundary stated clearly enough?
- Are the builtin rules a reasonable way to expose ordinary mathematical
  background?
- Does the fact-oriented interface remove meaningful proof-engine bookkeeping?
- Which interface ideas could be useful in other theorem-proving or
  autoformalization systems?
- Which parts of the current design are too ad hoc to scale?
