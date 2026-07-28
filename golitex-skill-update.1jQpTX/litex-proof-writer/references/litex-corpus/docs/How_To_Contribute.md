# How to Contribute to Litex

Jiachen Shen and The Litex Team, 2026-06-02. Email: litexlang@outlook.com

Markdown source: https://github.com/litexlang/golitex/blob/main/docs/How_To_Contribute.md

Litex is experimental. The most helpful contributions right now are simple:

1. Tell us where the documentation is confusing.
2. Help improve the dataset and textbook translation work.

You do not need to know the Rust kernel to help.

## 1. Tell Us Where the Docs Are Bad

Fresh-reader feedback is very useful. Read a small part of the README, Manual,
Mechanics notes, examples, or website docs, then report exactly where you got
confused.

A good report says:

- which page or example you read;
- the first sentence, concept, or code block that was unclear;
- what you expected it to mean;
- what output, error message, or explanation was confusing;
- what would have made the page easier to follow.

Small reports are enough. One clear confusion point is more useful than a broad
comment like "the docs are hard to read."

## 2. Work on Datasets or Textbooks

The datasets and textbooks Litex wants to explore are tracked here:

https://github.com/litexlang/datasets_and_textbooks

If you are interested, you can update that repository or pick something from
it. The work has two main directions:

- **Horizontal work: datasets.** Improve or expand problem datasets such as
  MATH500, miniF2F-style problems, high-school math, contests, and exams.
- **Vertical work: textbooks.** Translate a mathematical book or chapter in
  order, preserving the source structure and recording what Litex can or cannot
  express yet.

Useful things to do:

- improve existing data: fix statements, clean Litex code, update statuses,
  remove bad records, or make proof attempts clearer;
- fill missing work: add sources that are not listed yet, choose a first
  20-50 item slice, or add missing translated items;
- record blockers: when something cannot be verified, explain why and keep the
  smallest useful reproduction or note;
- add license notes when source text cannot be redistributed.

For each translated item, record the math idea before the Litex code like this:

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

Use `checkable` only when the `.lit` file verifies. Use `translated` when the
statement is natural but the proof is unfinished. Use `blocked` when the reason
is understood and recorded.

## What to Avoid at First

Please do not start by changing the verifier, parser, builtin rules, or
soundness-critical logic unless you already understand that part of the code.
For new contributors, documentation feedback and dataset/textbook work are much
better first contributions.

## Help Make Litex Easier to Understand

Another useful contribution is to make the project easier for outsiders to
understand. Good documentation, demos, and reports should answer questions like:

- What can Litex already run?
- How is Litex different from Lean or ordinary LLM problem solving?
- What is the strongest current demo?
- Which mathematical examples are already `checkable`?
- Which parts are `blocked`, and what do those blockers teach us?
- How can another person get involved?

If you improve a README section, demo note, benchmark page, or contribution
guide so that one of these questions becomes clearer, that is a useful
contribution.
