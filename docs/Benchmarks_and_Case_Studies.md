# Benchmarks and Case Studies

Jiachen Shen and The Litex Team, 2026-05-21. Email: litexlang@outlook.com

Markdown source: https://github.com/litexlang/golitex/blob/main/docs/Benchmarks_and_Case_Studies.md


## Purpose

Litex needs reproducible evidence, not only examples that look good in a page.
Benchmarks should let humans and agents run the same tasks, compare verifier
feedback, and measure progress over time.

The current best source of tasks is The Mechanics of Litex Proof. It contains
many textbook-style examples, from short calculations to larger function and
set arguments.

## Benchmark Levels

A useful Litex benchmark suite should be layered:

1. **Syntax and well-definedness.** Can the system or agent write meaningful
   Litex expressions with correct scopes and domains?
2. **Single fact verification.** Can a line be proved from builtin rules or
   a small context?
3. **Local proof repair.** Given an `unknown` or `error`, can the next attempt
   add the missing fact or fix the malformed expression?
4. **Proof skeleton completion.** Given a proof with precise `know` gaps, can
   those gaps be replaced by checked claims?
5. **Full theorem formalization.** Can a readable proof plan become a complete
   checked Litex proof?

This structure separates language understanding, mathematical reasoning,
verifier interaction, and longer proof planning.

## Task Record

Each benchmark item should record:

- source theorem or exercise;
- informal proof plan when available;
- starting Litex file or skeleton;
- expected checked proof;
- allowed `know` policy;
- verifier command used;
- final status;
- number of verifier calls;
- number of `unknown` and `error` results;
- number and shape of remaining `know` facts;
- runtime and tool version.

The most important policy is the `know` policy. A task should say whether
`know` is forbidden, allowed only for named background facts, or allowed as
temporary proof debt during repair but not in the final answer.

## Current Case Studies

Good first case studies:

- syllogism with a known `forall` fact;
- arithmetic and equality chains;
- finite set membership and case splits;
- existential witnesses;
- function equality and function application;
- subset and set-builder arguments;
- induction examples;
- the Chapter 8 `N^2 -> N` bijection using Cantor pairing.

The Chapter 8 bijection should be treated as the flagship larger case study.
It exercises enough of the language to show whether fact-oriented repair
actually scales beyond tiny examples.

## AI Evaluation

For AI agents, the benchmark should measure interaction, not just final success:

- how many attempts are needed;
- which failures are `unknown` versus `error`;
- whether the agent reduces proof debt over time;
- whether added facts are mathematically local and readable;
- whether final proofs avoid broad unchecked assumptions.

The goal is to test whether Litex gives useful verifier feedback. A failed
attempt can still be valuable if it shows where the proof plan needs a smaller
fact.

## Desired Command Shape

A future benchmark command should make reproduction simple:

```bash
litex bench benchmarks/mechanics
```

or:

```bash
python3 The-Mechanics-of-Litex-Proof/extract_examples_from_md_files.py
```

The output should eventually summarize:

- checked tasks;
- failed tasks;
- unknown facts;
- malformed statements;
- remaining proof debt;
- builtin and known-fact proof paths;
- runtime.

The exact command can evolve, but the benchmark should always be easy to run
from a fresh checkout.

## What This Evidence Can Support

Benchmarks should support modest claims:

- Litex can check a growing set of textbook-style proofs.
- Litex gives local feedback that humans and agents can use.
- Certain proof patterns become shorter or more direct in a fact-oriented
  interface.
- Some failures reveal missing background facts or missing builtin support.

Benchmarks should not be used to claim that Litex is production-ready or that
it replaces mature proof assistants.
