# Renaissance AI for Math Fund Application Draft

Jiachen Shen and The Litex Team, 2026-06-03. Email: litexlang@outlook.com

Markdown source: https://github.com/litexlang/golitex/blob/main/docs/Renaissance_AI_for_Math_Fund_Application.md

## One-Sentence Pitch

Litex is an open-source, fact-oriented proof language and verifier for making
checked mathematics cheap enough for mathematicians, students, and AI agents to
produce useful formal data at scale.

## Why This Fits AI for Math

The Renaissance AI for Math Fund is a natural fit because Litex sits at the
intersection of three fund-relevant needs:

- **Tools for mathematicians.** Litex is designed around mathematical objects,
  facts, and local verifier feedback, not tactic-state programming as the first
  user experience.
- **Datasets and benchmarks.** Litex examples can record a full pipeline:
  natural-language idea, formal statement, checked proof, verifier output, and
  explicit blockers.
- **Open infrastructure.** The project can produce open-source code, open
  checked examples, and reusable benchmark slices for AI-assisted mathematical
  reasoning.

The proposal should not present Litex as a replacement for Lean, Coq, Isabelle,
or Mathlib. The stronger claim is narrower and more credible: Litex tests
whether a smaller, readable, fact-oriented formal surface can reduce the cost of
producing checked mathematical data.

## Fund Fit Notes as of 2026-06-03

Source checked: https://www.renaissancephilanthropy.org/ai-for-math-fund

The Renaissance AI for Math Fund currently describes its primary subgranting
work as support for projects applying AI and machine learning to mathematics,
including technical research, new ML-for-math paradigms, and critical tools that
empower mathematicians. The main grants are described as $100K-$1M awards for
12-24 months of work, with open-access code, datasets, and research outputs.

The same page also describes rolling seed grants up to $100K for early-stage
research or prototypes in automated theorem proving, AI-assisted proof
development, mathematical reasoning, datasets and benchmarks, tooling
infrastructure, and field-building resources.

Litex should therefore be framed either as:

- a **full infrastructure grant** for an open verifier, checked-example corpus,
  benchmark pipeline, and AI proof-repair evaluation suite; or
- a **seed grant** for hardening the quotient-group demo, producing a first
  benchmark slice, and publishing a short public evaluation report.

## Core Demonstration: Quotient Groups From First Principles

The new flagship example is the checked quotient-group development in
`examples/04_structures/group_quotient.lit`. It defines and verifies a local
algebraic world from first principles:

- group laws and a `Group` structure;
- subgroups and normal subgroups;
- left cosets and quotient sets;
- quotient multiplication on cosets;
- representative independence and well-definedness;
- a concrete instance for the real additive group modulo `{0}`.

This is a meaningful upgrade over small arithmetic demos. Quotient groups are a
standard undergraduate abstract algebra construction. The example shows that
Litex can express and check a nontrivial mathematical development without
depending on a large pre-existing algebra library.

Suggested application language:

> We recently completed a checked quotient-group development in Litex. The file
> defines groups, subgroups, normal subgroups, left cosets, quotient sets,
> quotient multiplication, and proves the representative-independence condition
> needed for the induced operation. It then instantiates the construction on the
> real additive group modulo `{0}`. The point is not that quotient groups are new
> mathematics; the point is that Litex can express and check a standard
> undergraduate abstract algebra construction from first principles, without
> relying on a large pre-existing algebra library.

Follow-up sentence:

> This is exactly the kind of artifact we want to scale: readable, checked
> mathematical data that a mathematician can inspect, an AI model can learn
> from, and a verifier can audit.

## What the Example Proves About Litex

### 1. Litex can build a local mathematical world

The quotient-group file does not import a ready-made algebra hierarchy. It
builds the required interface in the file itself, in the order a textbook or
course would introduce it. This supports the proposal claim that Litex is useful
for bootstrapping formal mathematics in areas where a mature library is not yet
available.

### 2. Litex has a mathematician-native proof surface

The key objects look like ordinary mathematics:

```text
g &Group<s>
h power_set(s)
$is_normal_subgroup(s, g, h)
$is_group_quotient_set(s, g, h, q)
$is_quotient_multiplication(s, g, h, q, quotient_mul)
```

A reader does not need to first learn a large type-theoretic API, a tactic
language, or a library naming convention. The proof proceeds by stating the next
mathematical fact and letting the verifier check it against the current context.

### 3. Litex data is useful for AI systems

The example records the reasoning path in a form that is close to natural
mathematical proof:

1. define the concepts;
2. prove local lemmas;
3. establish unique existence;
4. build a function from the unique-existence theorem;
5. expose a reusable interface theorem;
6. instantiate the construction in a familiar group.

This structure is valuable for AI training and evaluation because it tests more
than theorem-name retrieval. A model must track definitions, hypotheses,
well-definedness, witnesses, and reusable facts.

### 4. Litex complements mature proof assistants

Lean and Mathlib remain stronger for library depth, abstraction, and large
formalization projects. Litex makes a different bet: many ordinary mathematical
arguments may be cheaper to write and repair if the main interface is facts,
objects, and verifier feedback rather than tactic-state navigation. The grant
proposal should frame Litex as complementary infrastructure, not as a
replacement.

## Proposed Grant Work Plan

### Full proposal shape, 12-24 months

Build Litex into an open, reproducible AI-for-math data and tooling pipeline:

1. **Verifier and language hardening.**
   Improve diagnostics, well-definedness checks, builtin/infer rule
   documentation, and regression coverage around examples like quotient groups.

2. **Checked example corpus.**
   Produce 100-300 checked Litex examples across algebra, elementary number
   theory, set theory, analysis fragments, and contest-style reasoning.

3. **Translation and benchmark pipeline.**
   Convert selected items from Mathematics in Lean, MATH500, MiniF2F,
   high-school math, Tao Analysis, and other sources into structured Litex
   records with status labels: `translated`, `checkable`, or `blocked`.

4. **AI evaluation artifacts.**
   Publish tasks where an AI system must produce or repair Litex proofs from a
   natural-language proof idea, with verifier feedback and blocker labels.

5. **Public documentation and demos.**
   Turn flagship examples, including quotient groups, into readable documents
   for mathematicians and AI-for-math researchers.

### Seed-grant shape, up to 6-9 months

If applying to a smaller seed-grant track, compress the request to a concrete
prototype milestone:

- harden the quotient-group example into a public flagship demo;
- create 25-50 structured Litex benchmark items;
- build a repeatable runner that reports checked, translated, and blocked
  status;
- publish a short benchmark report and a demo path for AI proof repair.

## Deliverables

The deliverables should be concrete and auditable:

- open-source Litex verifier improvements;
- checked example files under `examples/`;
- structured benchmark records with natural-language idea, Litex code, proof
  attempt, status, blocker label, and verifier command;
- public documentation for mathematicians;
- a small report summarizing checked examples, blockers, and reusable proof
  patterns;
- optional AI-agent evaluation scripts that attempt proof repair against the
  verifier.

## Evaluation Criteria

Use metrics that match Litex's actual thesis:

- number of fully checked examples;
- number of translated but blocked examples, with blocker labels;
- fraction of examples that avoid `know` in the final proof;
- verifier calls needed to repair representative tasks;
- clarity of verifier output for failed tasks;
- number of reusable proof patterns extracted from completed examples;
- number of tasks suitable for AI proof-generation or proof-repair evaluation.

Avoid overclaiming against mature theorem provers. The right evidence is not
"Litex is stronger than Lean"; it is "Litex may make some kinds of checked
mathematical data cheaper to produce, inspect, and repair."

## Suggested Abstract

Litex is an experimental open-source proof language and verifier for
fact-oriented formal mathematics. Its goal is to make checked mathematical
reasoning easier to write, inspect, and repair by mathematicians, students, and
AI agents. Instead of requiring users to begin with a large type-theoretic API or
tactic workflow, Litex lets them build local mathematical worlds from objects,
definitions, facts, and explicit proof steps.

Recent progress shows that this approach is no longer limited to small
arithmetic examples. We have completed a checked quotient-group development that
defines groups, normal subgroups, cosets, quotient sets, quotient
multiplication, representative independence, and a concrete real-additive-group
instance modulo `{0}` from first principles. This example demonstrates the core
promise of Litex: readable formal mathematics that can be audited by a verifier
and used as structured data for AI systems.

With support from the AI for Math Fund, we will turn this prototype into an open
AI-for-math infrastructure project: hardening the verifier, producing a corpus
of checked mathematical examples, building structured benchmark records, and
publishing reusable datasets for proof generation and proof repair. The project
is complementary to Lean and Mathlib. Its purpose is to test whether a smaller,
fact-oriented formal surface can make useful checked mathematical data cheaper
to produce at scale.

## Suggested Short Answer: "Why Now?"

The quotient-group example is the first strong signal that Litex can carry a
serious mathematical development, not only isolated calculations. It gives the
proposal a concrete artifact reviewers can inspect and run. The next step is to
scale from one serious example to a reproducible corpus: many small-to-medium
mathematical developments, each with checked proof status, verifier output, and
explicit blocker labels. This is exactly the kind of data infrastructure that AI
for Math needs but does not get from informal proofs alone.

## Suggested Short Answer: "Why Not Just Lean?"

Lean and Mathlib are mature, powerful, and essential to the future of formal
mathematics. Litex explores a different layer. Many mathematicians and AI agents
need a low-friction way to write local mathematical facts, receive verifier
feedback, and produce structured formal data without first navigating the full
complexity of a large type-theoretic ecosystem. Litex can serve as a readable
front layer, a benchmark generator, and a proof-repair environment whose outputs
may later inform or interoperate with deeper proof-assistant ecosystems.

## Risk and Mitigation

- **Risk: Litex has a larger trusted verifier surface than small-kernel systems.**
  Mitigation: document builtin and infer rules, add regression tests, expose
  proof explanations, and avoid hiding assumptions.

- **Risk: examples remain too small.**
  Mitigation: use quotient groups as the new baseline for meaningful examples,
  then expand through algebra, number theory, set theory, and analysis slices.

- **Risk: AI-generated proofs become unverifiable text.**
  Mitigation: every dataset item must include verifier status, exact commands,
  and blocker labels. Generated proof attempts are useful only when checked or
  explicitly classified.

- **Risk: the project is misunderstood as competing with Lean.**
  Mitigation: state clearly that Litex is complementary. The fundable hypothesis
  is lower-cost production of readable checked data, not replacement of mature
  proof assistants.
