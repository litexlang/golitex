# How to Contribute to Litex

Jiachen Shen and The Litex Team, 2026-06-02. Email: litexlang@outlook.com

Markdown source: https://github.com/litexlang/golitex/blob/main/docs/How_To_Contribute.md

Litex is experimental. The most useful early contributions are small, concrete
reports from real use: run examples, read documentation, try a proof, and record
where the feedback loop succeeds or breaks.

Good contributors do not need to know the Rust kernel. It is enough to know
some undergraduate mathematics and be willing to report precise evidence.

## Good First Contributions

### Documentation Feedback

Read a small section of the docs and report:

- the first unclear sentence or example;
- a concept that appears before it is explained;
- duplicated, outdated, or inconsistent pages;
- a code block that is hard to modify;
- verifier output that does not suggest a next step.

### Example Runner Pass

Pick a small examples folder, run the `.lit` files, and report:

- which examples pass;
- which examples are slow, noisy, or confusing;
- which comments or names are misleading;
- one concrete improvement to the example or docs.

### Minimal Blockers

If a proof step is mathematically obvious but Litex cannot verify it, reduce it
to a 10-30 line runnable example.

Include:

- what you expected Litex to prove;
- what Litex actually reported;
- the smallest context needed to reproduce it;
- one blocker label.

Useful labels:

- `blocked_by_language`
- `blocked_by_stdlib`
- `blocked_by_infer_rule`
- `blocked_by_kernel`
- `blocked_by_syntax`
- `blocked_by_diagnostics`
- `blocked_by_formulation`

### Small Checkable Examples

Write a small `.lit` file that demonstrates one theorem, feature, or proof
pattern. Good examples are usually 10-30 lines and have no hidden proof debt.

Useful topics include finite sets, function equality, integer divisibility,
basic inequalities, simple `by thm` usage, and short set arguments.

## Dataset and Textbook Translation

Litex is being developed by pressure-testing real mathematics. Good sources
include MATH500, miniF2F-style problems, high-school math, undergraduate
textbooks, Tao Analysis, Weil number theory, and selected contest problems.

For every translated item, record the mathematical idea before the Litex code:

```yaml
id:
source:
topic:
difficulty:
natural_language_idea:
litex_code:
proof_attempt:
status: translated/checkable/blocked
blocker:
notes:
```

Use these statuses:

- `checkable`: the `.lit` file verifies successfully.
- `translated`: the statement is naturally expressed, but proof work remains.
- `blocked`: the failure reason is understood and recorded.

Do not submit only raw Litex code. If the source text cannot be redistributed,
write a reusable mathematical reformulation and note the license concern.

## Dataset and Textbook Planning Document

The datasets and textbooks Litex currently wants to explore are tracked here:

https://github.com/litexlang/datasets_and_textbooks

You may update that repository through pull requests. Useful updates include:

- adding a dataset, textbook, contest, exam, or problem family;
- marking a source as high priority, low dependency, blocked, or redundant;
- recording license or redistribution concerns;
- linking a source to a translation workspace, example, or blocker;
- proposing a 20-50 item slice for a first experiment.

Keep updates concrete enough that another contributor can pick the next small
translation slice and understand why it matters.

## What Not to Start With

Avoid these until you have more local context:

- changing the Rust verifier or parser;
- adding builtin or infer rules;
- changing soundness-critical logic;
- reorganizing the standard library;
- starting long textbook proofs before isolating blockers;
- hiding proof gaps with broad `know` facts.

## A Useful First Week

1. Read the first few Mechanics chapters.
2. Run a few examples locally.
3. Write five concrete documentation confusion points.
4. Modify one example and inspect the verifier output.
5. Turn the first serious failure into a minimal blocker.
6. If there is time, translate one small problem.
