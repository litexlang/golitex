# How to Contribute to Litex

Jiachen Shen and The Litex Team, 2026-06-02. Email: litexlang@outlook.com

Markdown source: https://github.com/litexlang/golitex/blob/main/docs/How_To_Contribute.md

Litex is experimental. The most helpful contributions right now are simple:

1. Tell us where the documentation is confusing.
2. Help improve the dataset and textbook translation work. See https://github.com/litexlang/litex-math500 and https://github.com/litexlang/litex-minif2f

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

The best first dataset contribution is concrete, runnable proof work on
MiniF2F and MATH500:

- https://github.com/litexlang/litex-minif2f
- https://github.com/litexlang/litex-math500

There are two useful kinds of dataset work:

1. Finish unfinished problems by removing or reducing `proof_debt`.
2. Improve already finished problems when the code is too long, unclear, or
   semantically weaker than the source problem.

Quality matters more than count. A small number of checkable, readable files is
more useful than a large set of broad suggestions.

### Finish Unfinished Problems

A strong result is a fully checkable `.lit` file with no non-background `proof_debt`.
A useful partial result is also acceptable: if the original proof had one broad
`proof_debt`, split it into several smaller mathematical steps, prove the steps you
can, and leave only the precise blocked step as `proof_debt`.

For any remaining `proof_debt`, add a short comment in the `.lit` file explaining:

- what exact mathematical step is still missing;
- why the current proof attempt does not close it;
- whether it looks like `proof_debt` or `kernel_problem`.

### Improve Finished Problems

Already-finished files can still be useful contributions if you make them
mathematically stronger or easier to read. Good improvements include:

- strengthening a statement that was weaker than the source problem;
- removing assumptions that hide too much mathematical content;
- shortening a proof without making it less explicit;
- making the proof more Litex-native;
- replacing repeated local clutter with a small clear claim.

Do not submit cosmetic-only changes.

### Textbook Work Is A Harder Next Step

Textbook formalization is valuable, but it is usually harder than dataset work
because a chapter has local definitions, source order, omitted proofs, examples,
and long dependency chains. If you want to work on a textbook, first read
`https://litexlang.com/doc/Tutorial/Textbook_Formalization_Guide`.

That guide explains how to split a chapter into `narrative`, `object
definition`, `prop definition`, `thm`, and `example sketch` items before writing
Litex code.

Try help with https://github.com/litexlang/litex-analysis-textbook .

## What to Avoid at First

Please do not start by changing the verifier, parser, builtin rules, or
soundness-critical logic unless you already understand that part of the code.
For new contributors, documentation feedback and dataset/textbook work are much
better first contributions.

## Kernel-Facing Cleanup Checklist

When changing kernel-facing syntax or adding a statement form, keep the whole
flow in sync. A statement is not complete just because one parser branch exists.
Check the representation, parser, executor, output, tests, and documentation
together.

For a new or renamed statement form:

- Add the statement data structure and place it in the appropriate `Stmt`
  subgroup.
- Add parser support and a clear parse error for legacy or invalid spellings.
- Add executor support, or explicitly route unsupported forms to a clear error.
- Update display, metadata, JSON/output evidence, and LaTeX output if the form
  can be shown to users.
- Add focused regression coverage for the success path and the most important
  rejected spelling or malformed input.
- Update the Manual or examples when the user-facing syntax changes.

Prefer a small end-to-end change over a partial branch in only one layer. If the
statement interacts with verification, imports, or proof blocks, run the
broader verifier test suite before treating it as complete.

Some small facts may be intuitive but hard to formalize because Litex's
standard library is still missing supporting lemmas. For now, collect these
cases and mark them uniformly with `proof_debt`. For example, many files use
`finite_set_sum`, and a common fact is that permuting the same finite set should
not change the result. It is acceptable to leave such facts as `proof_debt` for now:
they are tedious to prove and do not block the main translation work. After the
main line is complete, clean up these `proof_debt` steps together; some should become
standard-library facts, and others should be proved locally.

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


## Reference

Here are videos on how to use AI to generate Lean code. Lean is a mature formalization system for mathematics. Although the first principle of Litex and Lean are different, we can still learn a lot from Lean on how to use AI to generate code.

1. Terrence Tao on how to use claude code to write lean: https://www.youtube.com/watch?v=JHEO7cplfk8

2. How mathematicians use lean: https://www.youtube.com/watch?v=I2zaPoj3G50&list=WL
