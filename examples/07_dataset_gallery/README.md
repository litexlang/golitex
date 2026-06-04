# Dataset Gallery

This folder collects small, runnable Litex examples selected from the local
translation workspaces under `scripts/`. Each dataset or book has one Markdown
gallery page, and every `litex` fenced block in those pages is part of the
normal `cargo test run_examples` suite.

Each item starts with a translation record block containing `id`, `source`,
`topic`, `difficulty`, `natural_language_idea`, `litex_code`, `proof_attempt`,
`status`, `blocker`, and `notes`.  Gallery items are selected from finished or
locally checkable snippets; unfinished attempts with `know`, `abstract_prop`, or
placeholder proofs are intentionally left out.

Pages:

1. [`math500.md`](math500.md) - 21 finished MATH-500 examples across algebra, number theory,
   geometry, precalculus, and counting.
2. [`minif2f.md`](minif2f.md) - 20 finished miniF2F examples covering AMC/AIME/IMO-style,
   algebra, number theory, and induction problems.
3. [`gsm8k.md`](gsm8k.md) - 20 arithmetic word-problem derivations.
4. [`math23k.md`](math23k.md) - 20 Chinese arithmetic word-problem derivations.
5. [`metamathqa.md`](metamathqa.md) - 20 generated arithmetic/algebra QA derivations.
6. [`high_school_book.md`](high_school_book.md) - 20 high-school textbook snippets, including the 14
   existing verifier-evidence items plus 6 additional runnable gallery items.
7. [`analysis_one.md`](analysis_one.md) - 20 Tao Analysis I micro-examples from the currently
   checked parts of chapters 2, 3, 4, 5, and 9.
8. [`number_theory_for_beginners.md`](number_theory_for_beginners.md) - 20 Weil number-theory snippets from the
   local Chapters I-IV pressure-test files.

Run all examples with:

```bash
cargo test run_examples -- --nocapture
```
