# Outreach Guide

Jiachen Shen and The Litex Team, 2026-05-21. Email: litexlang@outlook.com

Markdown source: https://github.com/litexlang/golitex/blob/main/docs/Outreach_Guide.md


## Core Pitch

> Litex is a fact-oriented formal language where users write ordinary
> mathematical facts, and the verifier grows an explainable checked context;
> this makes textbook-style formalization easier for humans and gives AI agents
> a local feedback loop for repairing proofs.

Use the same first half for every audience. Change the final emphasis.

## Formal Mathematicians and Proof Assistant Researchers

Emphasize:

- fact-oriented interface for ordinary mathematical reasoning;
- well-definedness, builtin rules, known facts, and known `forall` facts;
- intentional narrowness compared with Lean, Coq, and Isabelle;
- The Mechanics of Litex Proof, especially the `N^2 -> N` bijection;
- open questions about soundness boundary and builtin rule design.

Ask for feedback on:

- whether the soundness boundary is clear;
- whether the builtin rule design is acceptable;
- whether this is a valuable proof interface experiment.

Do not lead with broad claims about AI changing mathematics.

## AI and Formal Math Researchers

Emphasize:

- Litex as an agent-facing formal language;
- local verifier statuses: `true`, `unknown`, `error`;
- `verified_by` as proof-path feedback;
- `know` as explicit proof debt;
- Chapter 8 as a case study for iterative proof repair.

Ask for feedback on:

- whether fact-level feedback improves proof repair;
- how to turn Mechanics examples into benchmark tasks;
- what logs would be useful for training and evaluation.

## Lean Community

Emphasize:

- Lean is mature and has Mathlib;
- Litex is not competing on library depth;
- Litex explores a complementary interface: fact-oriented, set-theoretic,
  context-growing proof scripts;
- Litex may be useful as a preformal, pedagogical, or agent-facing layer.

Ask for feedback on:

- which interface ideas are useful;
- which ideas could complement Lean tooling or AI formalization workflows;
- which trade-offs are stated unfairly or unclearly.

Avoid saying or implying that Litex proves Lean is too complex.

## Lean and AI for Math Researchers

Emphasize:

- Litex as a possible intermediate representation;
- agents may produce Litex proof skeletons before full Lean formalization;
- fact-level feedback may help proof planning and debugging;
- Mechanics examples can become measurable benchmark tasks;
- verifier output can be logged as training or evaluation signal.

Research question:

> Does fact-level feedback improve autoformalization success compared with
> tactic-level interaction alone?

## AI for Science

Emphasize:

- Litex as a checkable mathematical notebook for derivations;
- formulas stay close to domain notation;
- LLMs can translate paper or textbook derivations into local checked facts;
- good first targets are applied math, physics, engineering, and optimization
  derivations;
- the goal is verifier feedback for AI-generated scientific reasoning.

Avoid theorem-prover internal details unless the audience asks.

## Domestic Leadership and Project Partners

Use Chinese and emphasize strategic value:

- Litex 是面向 AI 可验证数学推理的开源基础设施；
- 它降低形式化数学门槛；
- 它让教材证明、科学推导和 AI 生成推理可以被机器检查；
- 已有 playground、manual、教材化案例、Rust/Python 接口和数据集方向；
- 下一步是稳定 kernel、扩充数学库、建设 benchmark 和 agent workflow。

Main framing:

> AI for Science 需要可验证反馈环境。Litex 可以成为让 AI 数学推理从“看起来对”变成“可检查”的基础层。

## Education and Textbook Readers

Emphasize:

- Litex proof scripts look close to textbook reasoning;
- students can see which facts are accepted, unknown, or malformed;
- examples can be run directly;
- The Mechanics of Litex Proof is the main entry point.

Ask for feedback on:

- whether examples teach proof structure clearly;
- which textbook topics should be added next;
- whether verifier output helps students understand proof steps.

## Short Message Templates

Formal methods:

> I am working on Litex, a fact-oriented formal language for ordinary
> mathematical reasoning. It is intentionally narrower than Lean/Coq/Isabelle:
> users state mathematical facts, and the verifier checks well-definedness,
> builtin rules, known facts, and known universal facts. I would value feedback
> on the soundness boundary, builtin rule design, and whether this is a useful
> proof-interface experiment.

AI and formal math:

> I am exploring Litex as an agent-facing formal language. The verifier returns
> local feedback on whether each fact is true, unknown, or malformed, and
> successful lines include proof-path explanations. The main question is
> whether this fact-level feedback helps agents repair textbook-style proofs.
> The strongest current case study is the Chapter 8 `N^2 -> N` bijection.

Lean community:

> Litex is not trying to replace Lean or compete with Mathlib. It explores a
> different proof UX: fact-oriented, set-theoretic, context-growing proof
> scripts that may be useful as a pedagogical, preformal, or agent-facing layer.
> I would appreciate feedback on which interface ideas are actually useful and
> which trade-offs are stated unfairly.

AI for Science:

> Litex can be used as a checkable mathematical notebook for local derivations.
> An LLM can translate a paper or textbook derivation into Litex facts, run the
> verifier, and repair lines that are unknown or malformed. The goal is to add a
> verifier feedback layer to AI-generated scientific reasoning.

Domestic strategy:

> Litex 是面向 AI 可验证数学推理的开源基础设施。它让数学证明、教材推理和 AI 生成推导可以被机器逐步检查。当前已有 playground、manual、教材化案例和接口方向，下一步应重点稳定 kernel、扩充数学库、建设 benchmark 和 agent workflow。

## Phrases to Avoid

- "Litex replaces Lean."
- "Litex is production-ready."
- "AI will solve formal mathematics by itself."
- "The theorem is hard because Lean cannot do it."
- "The trusted base does not matter."

Use a narrower and more accurate line: Litex is an early but concrete
experiment in fact-oriented proof interfaces and agent-facing verifier
feedback.
