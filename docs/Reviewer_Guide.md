# Reviewer Guide

Jiachen Shen and The Litex Team, 2026-06-04. Email: litexlang@outlook.com

Markdown source: https://github.com/litexlang/golitex/blob/main/docs/Reviewer_Guide.md


## Purpose

This guide is for human and AI reviewers who want to evaluate Litex without
accidentally changing the question being asked.

Litex is not trying to replace Lean, Coq, Isabelle, or other small-kernel proof
assistants. It tests a different hypothesis: that a readable, fact-oriented
surface language, backed by a larger trusted mathematical checker, can make
checked mathematical work cheaper for students, domain scientists, and AI
agents.

A useful review should therefore evaluate both sides of the project:

1. whether the fact-oriented interface creates a shorter checked feedback loop;
2. whether the trusted boundary is visible enough to audit.

Counting every trusted rule, unfinished proof gap, or missing library theorem as
an independent failure misses the point. Those risks matter, but they should be
weighed against the interface benefit, the reproducible corpus, the benchmark
translation loop, and the explicit blocker map.


## Correct Frame

Review Litex as a fact-oriented proof interface experiment.

The first principles are:

- users write mathematical facts directly;
- the verifier grows a checked context top to bottom;
- later facts are checked by well-definedness, builtin rules, known facts, and
  known `forall` facts;
- matching and substitution are central mechanisms, not incidental automation;
- `unknown` is useful feedback: it usually means the proof needs a smaller
  intermediate fact, a missing hypothesis, or a library/background theorem.

The intended audience is broad: students, domain scientists, AI agents, and
mathematically trained users who may not become Lean or Coq experts. Litex may
also be interesting to proof-assistant researchers, but it is not optimized for
the same trust model, ecosystem maturity, or abstraction style as mature proof
assistants.


## Trusted Boundary

Litex has a larger trusted base than a small-kernel proof assistant. That is an
intentional design trade-off at the prototype stage.

When reviewing the trusted boundary, separate these questions:

- Are the builtin rules mathematically clear?
- Are their well-definedness conditions explicit?
- Are they implemented correctly?
- Are they tested well enough?
- Does verifier output explain which rule or known fact closed a goal?

Do not treat the existence of builtin rules as the criticism by itself. Builtin
rules are Litex's basic verification mechanism. They represent ordinary
mathematical steps such as arithmetic simplification, equality substitution,
membership in displayed sets, order consequences, function application
well-definedness, set inclusion, and tuple projections. The real review target
is whether those rules are specified, implemented, tested, and explained well.

The standard library currently contains many `know` facts. This is also not a
hidden claim that every background theorem has already been proved inside
Litex. `know` records an accepted background fact, axiom, or proof-debt item. A
serious review should classify remaining `know` facts as:

- accepted background for the intended theory;
- temporary proof debt to be replaced later;
- a risky assumption that should block a stronger claim.

Use `-strict` for assumption-sensitive runs when appropriate. Strict mode
rejects user `know` statements after builtin initialization, but it does not
remove the builtin trusted base or imported-module dependencies.


## Evidence To Inspect

A complete review should inspect more than the README.

Minimum public evidence:

- `README.md`: first-contact positioning and examples;
- `docs/Manual.md`: syntax, proof process, builtin rules, and builtin
  inference;
- `docs/Soundness_and_Limitations.md`: trusted base, `know`, strict mode, and
  current limitations;
- `docs/Research_Positioning.md`: research hypothesis and non-goals;
- `docs/Benchmarks_and_Case_Studies.md`: benchmark policy and evidence
  boundary;
- `examples/`: polished runnable examples;
- `benchmarks/`: cleaned public benchmark slices when available.

Private or external evidence should be named explicitly if it is used:

- dataset workspaces and generated `current_data.json` files;
- The Mechanics of Litex Proof corpus and its markdown runner;
- external dataset repositories;
- Hugging Face datasets;
- `litexpy` or other integration repositories.

If a reviewer only inspects `golitex` README material and does not inspect the
benchmark or dataset evidence, the review should say that its scope is limited
to first-contact documentation and local code structure.


## Required Review Record

Every serious review should record:

- commit hash, Litex version, operating system, and date;
- commands run and whether they passed, failed, or were not run;
- directories and external repositories inspected;
- claims reproduced by running the system;
- claims inferred only from reading source or documentation;
- number and role of remaining `know` facts in reviewed artifacts;
- whether `-strict` was used;
- blocker labels for failed translations or proof attempts;
- whether checkable items were verified with the relevant command.

Suggested commands for a fresh local review:

```bash
cargo test run_examples
cargo test run_the_mechanics_markdown_files
cargo test run_all
```

Use smaller targeted commands first when reviewing a narrow change. For
benchmark slices, use the verifier command recorded by the slice itself.


## Evaluation Axes

A useful review should separate these axes instead of collapsing them into one
score:

- **Language ergonomics:** Does the fact-oriented surface reduce proof-engine
  bookkeeping for ordinary mathematics?
- **Matching and substitution:** Do known facts and known `forall` facts let the
  user write the next mathematical fact directly?
- **Verifier feedback:** Does output explain why a fact succeeded, became
  `unknown`, or produced an `error`?
- **Trusted boundary:** Are builtin rules, infer rules, stdlib facts, and
  `know` dependencies visible?
- **Implementation correctness:** Are soundness-sensitive rules implemented
  defensibly and covered by tests?
- **Dataset throughput:** Can real problems be translated into
  `translated`, `checkable`, or `blocked` records with useful blocker labels?
- **Research value:** Do successes and failures produce evidence about the
  interface hypothesis?

An attack-surface-only review is incomplete. A large project will naturally
have more visible weak points. The relevant question is whether those weak
points are named, isolated, tested, and turned into a roadmap while the project
also demonstrates a distinctive capability.


## How To Read Benchmark Slices

Benchmark slices should not be judged only by final pass count.

For each item, check:

- natural-language proof idea or reformulation;
- Litex statement and proof attempt;
- status: `translated`, `checkable`, or `blocked`;
- verifier command and evidence for `checkable`;
- remaining `know` facts and their classification;
- primary blocker label for blocked items;
- whether the failure is a language, stdlib, builtin-rule, infer-rule,
  kernel, syntax, diagnostic, or formulation gap.

Failed items are useful when they produce small, actionable blockers. A
translation pipeline with clear failures can be more informative than a page of
unlabeled showcase examples.


## What Not To Claim

Do not claim that Litex is production-ready formal verification.

Do not claim that current standard-library `know` facts are all proved inside
Litex.

Do not claim that Litex replaces Lean, Coq, Isabelle, or Mathlib.

Do not claim that AI-generated mathematics becomes trustworthy merely by being
written in Litex. Litex can help decompose AI output into checkable facts,
surface malformed steps, expose assumptions, and turn failures into repair
tasks. The audit still depends on verifier output, trusted-boundary tracking,
and review of remaining assumptions.


## What A Strong Review Looks Like

A strong review says something like:

> I reviewed Litex as a fact-oriented checker, not as a small-kernel theorem
> prover. I ran the example and Mechanics tests, inspected the builtin-rule
> documentation and soundness boundary, sampled benchmark items, counted or
> classified remaining `know` dependencies, and separated implementation risks
> from the language-interface hypothesis.

That style of review can still be critical. It should be. But it gives useful
criticism without replacing Litex's research question with a different one.
