# AI Agent Workflow

Jiachen Shen and The Litex Team, 2026-05-21. Email: litexlang@outlook.com

Markdown source: https://github.com/litexlang/golitex/blob/main/docs/AI_Agent_Workflow.md


## Thesis

Litex is useful for AI agents because it exposes mathematical proof repair at
the level of local facts.

An agent does not only receive an opaque failure. It can see whether a line was
accepted, unknown, or malformed, and it can inspect how accepted facts were
verified. This makes Litex a practical interface for turning a readable proof
plan into a checked proof.

## What the Agent Sees

Every factual statement has one of three outcomes:

- `true`: the checker found a proof path;
- `unknown`: the statement is meaningful, but the checker does not yet have
  enough information;
- `error`: the statement is malformed or not well-defined.

For successful statements, Litex output can include `verified_by`, showing
whether the fact was closed by a builtin rule, a known fact, a known `forall`
fact, or another proof path. This is important training and debugging signal:
the agent sees not only that a line passed, but why it passed.

## `know` as Proof Debt

`know` adds a fact without verifying it. For ordinary final proofs, broad
`know` statements should be avoided or replaced by checked claims.

For agents, however, `know` is useful when treated as explicit proof debt. The
agent can write a precise missing fact, keep the proof skeleton readable, run
the checker, and then refine the debt into smaller checked steps.

This gives a practical workflow:

1. Write the natural-language proof plan.
2. Translate the plan into a Litex skeleton.
3. Use precise `know` facts only where the proof is not yet formalized.
4. Run Litex and inspect `true`, `unknown`, and `error` results.
5. Replace broad `know` facts with smaller claims or direct facts.
6. Repeat until the remaining assumptions are intentional background facts.

## Local Repair Loop

An agent should respond differently to each status:

- For `error`, fix syntax, scoping, well-definedness, or missing domain facts.
- For `unknown`, add a smaller intermediate mathematical fact: an equality,
  membership fact, domain condition, witness, case split, or relevant universal
  fact.
- For `true`, keep the accepted fact and use the `verified_by` explanation to
  understand which proof path worked.

This loop is close to ordinary mathematical debugging. The agent states the
next fact, checks it, and repairs only the local failure.

## Case Study

The key case study is the final Chapter 8 example in The Mechanics of Litex
Proof: a proof that there exists a bijection from `N^2` to `N` using Cantor
pairing.

The example matters because it is not a one-line puzzle. It requires a readable
plan, many local facts, function reasoning, tuple reasoning, arithmetic,
injectivity, surjectivity, and repeated refinement of proof debt. It shows the
kind of feedback loop Litex is designed to expose to an agent.

The claim is not that this theorem is difficult for mature proof assistants.
The claim is that Litex gives an agent a direct repair surface: failed lines
are local mathematical facts, not only tactic-state failures.

## Research Questions

The agent workflow should be evaluated with measurable questions:

- Does fact-level feedback reduce the number of failed repair attempts?
- Does `unknown` lead agents to add useful intermediate facts?
- Does `error` help agents fix well-definedness and scoping mistakes?
- Does explicit proof debt make partial proofs easier to complete?
- Can Litex proof skeletons later guide Lean or other mature formalizations?

## Recommended Logging

For experiments, keep logs that include:

- the source problem;
- the natural-language proof plan;
- every Litex attempt;
- verifier status per statement;
- `verified_by` output for accepted facts;
- all remaining `know` facts;
- number of verifier calls;
- final checked proof length.

These logs can become training data, evaluation data, or case studies for
agentic formal mathematics.
