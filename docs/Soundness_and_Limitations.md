# Soundness and Limitations

Jiachen Shen and The Litex Team, 2026-05-21. Email: litexlang@outlook.com

Markdown source: https://github.com/litexlang/golitex/blob/main/docs/Soundness_and_Limitations.md


## Purpose

Litex is experimental proof infrastructure. It is useful to ask what kind of
trust it is trying to provide, where that trust currently comes from, and where
the system is intentionally incomplete.

The short version is:

> Litex checks a proof by checking well-definedness, builtin mathematical
> rules, known facts, and known universal facts. It is useful as a
> fact-oriented proof interface experiment, but it should not yet be treated as
> production-grade formal verification.

This page is written for readers who care about proof assistant design,
foundations, and the boundary between a checked theorem and an assumed fact.

## What Litex Checks

A Litex proof grows a context. The user introduces objects, states facts, proves
local claims, names witnesses, splits cases, and records successful facts for
later use.

For each factual statement, Litex first checks whether the statement is
well-defined. Names must be in scope, function applications must satisfy domain
conditions, and expressions such as division must be meaningful. If this fails,
the statement is an error rather than a mathematical claim.

If the statement is well-defined, Litex tries to verify it from several sources:

1. builtin verification rules for equality, order, membership, numbers, sets,
   tuples, functions, and related ordinary mathematical concepts;
2. facts already known in the current context;
3. known `forall` facts whose statement shape matches the goal after
   substitution;
4. definitions and previously introduced properties that the checker is allowed
   to unfold or reuse.

A verified fact becomes part of the current context. Later statements can cite
it directly, use it through substitution, or use routine consequences inferred
from it.

## The Role of `know`

`know` is not a proof-producing command. It adds a fact to the current context
without checking it in that snippet.

This is deliberate. It supports several useful workflows:

- record an axiom or background theorem;
- write a readable proof skeleton before all gaps are formalized;
- mark exact proof debt and then refine it into checked claims.

The cost is also clear: if a false fact is introduced with `know`, later results
may depend on it. A Litex development that uses `know` should distinguish
checked facts from assumptions. For serious uses, the remaining `know` facts are
part of the trusted input, not consequences proved by Litex.

## Trusted Base

The current trusted base includes the parser, the object and fact
representations, the well-definedness checker, the verification engine, builtin
verification rules, builtin inference rules, and the code that records and
matches known facts.

This trusted base is larger and less minimal than the kernel of mature systems
such as Lean, Coq, or Isabelle. That is an intentional design trade-off at the
prototype stage: Litex puts more ordinary mathematical background into the
checker so that proof scripts can stay closer to textbook reasoning.

The important design question is not whether this trusted base is small today.
It is whether the boundary can be made explicit enough for users and
researchers to inspect:

- which facts are checked rather than assumed;
- which builtin rules are used;
- what mathematical property each builtin rule represents;
- which inferred facts are added after a statement succeeds;
- how universal facts are matched and instantiated.

## Builtin Rule Boundary

Builtin rules are meant to represent small, standard mathematical moves:
arithmetic simplification, equality substitution, membership in displayed sets,
order consequences, function application well-definedness, set inclusion, tuple
projections, and similar facts.

They are not meant to hide advanced theorem proving behind a black box. A good
builtin rule should have:

- a clear mathematical property;
- explicit well-definedness requirements;
- a small example;
- a visible explanation in verifier output when possible.

The risk is that a broad builtin rule can become too powerful or too implicit.
For this reason, builtin rules should be documented and tested as part of the
trusted mathematical background.

## Known Limitations

Litex is currently beta software. It is not ready for production or
mission-critical proof work.

Important limitations:

- Litex does not have the library depth of Mathlib.
- Litex is intentionally narrower than Lean, Coq, or Isabelle.
- Its foundational story is more pragmatic and set-theoretic at the surface.
- The trusted base is larger than a small proof kernel.
- `know` can introduce unchecked assumptions.
- Some mathematical areas still need better syntax, libraries, examples, and
  verifier support.
- The current examples are strong prototype signals, not a complete benchmark
  suite.

These limitations are part of the research value. Litex is exploring whether a
fact-oriented interface can make ordinary mathematical formalization and proof
repair easier.

## Current Evidence

The strongest public evidence is not one isolated theorem. It is the
textbook-style development in The Mechanics of Litex Proof: a full sequence of
runnable examples that exercise calculation, logic, induction, sets, functions,
relations, and longer proof repair.

This evidence is complemented by MATH500 and MiniF2F-style benchmark tasks.
Those tasks are useful because the library and kernel are still growing:
successful translations become examples or benchmarks, while failed
translations expose concrete language, standard-library, builtin-rule,
infer-rule, or diagnostic gaps.

Litex is not trying to be a faster Lean. It chooses a different proof
interface: for textbook-style mathematics, the user writes a sequence of
checkable facts, and the checker uses context plus builtin relationships to
keep the feedback loop short. *In a local run, more than 240 runnable examples
from The Mechanics of Litex Proof checked in about 13 seconds.*

## Feedback Wanted

Litex especially needs feedback on:

- whether the soundness boundary is clear enough;
- which builtin rules are mathematically safe and which are too implicit;
- whether the verifier output gives enough evidence for accepted facts;
- whether `know` is useful as explicit proof debt or too easy to misuse;
- whether the fact-oriented interface is a valuable experiment for formal
  proof writing.
