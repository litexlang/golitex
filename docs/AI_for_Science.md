# AI for Science

Jiachen Shen and The Litex Team, 2026-05-21. Email: litexlang@outlook.com

Markdown source: https://github.com/litexlang/golitex/blob/main/docs/AI_for_Science.md


## Thesis

Litex can act as a checkable mathematical notebook for scientific derivations.
The near-term target is not verifying entire scientific papers. It is checking
local chains of formulas, assumptions, inequalities, definitions, and
derivations that appear inside applied mathematics, physics, engineering, and
optimization.

For AI for Science, the key problem is not only generating formulas. It is
knowing when a generated derivation is locally valid.

## Why Litex Fits This Layer

Scientific derivations often use notation that is close to ordinary
mathematics:

- functions and parameters;
- sets and domains;
- tuples and indexed objects;
- sums and products;
- equalities and inequalities;
- existential choices and case splits.

Litex keeps many of these objects close to domain notation. A user can
write a derivation as a sequence of facts, then ask the checker which lines are
verified, unknown, or malformed.

This does not replace numerical simulation, symbolic algebra, or domain
software. It adds a verifier feedback layer for mathematical reasoning steps.

## Good First Applications

Litex is most suitable for local derivation checks such as:

- algebraic transformations in an applied model;
- inequality steps in an optimization proof;
- finite sums and products in discrete models;
- function-domain and parameter assumptions;
- elementary real-number reasoning;
- set and tuple manipulations in formalized definitions;
- proof sketches extracted from textbooks or papers.

These tasks are small enough to be checked locally but important enough to catch
hallucinated or skipped reasoning steps.

## Verification Workflow

A useful workflow is:

1. Extract a derivation from a paper, textbook, or model note.
2. Ask an LLM to rewrite the derivation as Litex facts.
3. Run the verifier.
4. Treat `error` as a syntax, scoping, or well-definedness problem.
5. Treat `unknown` as a missing mathematical step.
6. Add the missing local fact, domain condition, lemma, or assumption.
7. Keep the final derivation as a checked artifact with explicit assumptions.

This turns the broad problem of scientific reasoning hallucination into a more
local problem: each generated line must be a well-defined mathematical fact
that follows from the current context or is marked as an assumption.

## What to Build Next

The most useful next examples are not abstract theorem-prover demos. They are
short scientific derivations:

- an optimization inequality with all assumptions stated;
- a recurrence or finite sum identity;
- a physics-style algebraic derivation with domain restrictions;
- a small engineering formula transformation;
- an applied probability or combinatorics calculation.

Each example should show:

- the informal source derivation;
- the Litex version;
- which facts are checked;
- which facts remain as assumptions;
- how verifier feedback helped repair the derivation.

## Positioning

For AI for Science audiences, the pitch should be:

> Litex gives scientific reasoning a local verifier feedback loop.

Avoid leading with theorem-prover internals. The important point is moving from
"this derivation looks plausible" to "each local mathematical fact was checked
or explicitly marked as an assumption."

## Current Limitations

Litex still needs more applied examples and more domain-specific background
facts. It should begin with local derivations in applied math and science, not
with a claim to verify full modern scientific papers.

This narrower goal is still valuable: many scientific mistakes and AI
hallucinations happen in small algebraic, inequality, or domain-condition
steps.
