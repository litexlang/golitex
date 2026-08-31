# Analysis I: current runnable module

This is the current release-verified Analysis I translation. It exports the
project introduction, Chapters 1--11, and Appendix A in the original namespace
order. Chapters 8--11 have passed persistent source-order replay and their
registered canonical `-f` gates with exit 0 and top-level `ok=true`. The
synchronized formal mirror passes the same registered-file boundary.

The runnable module currently covers introductory mathematical language,
natural numbers, set theory, integers, and rationals. Representative public
interfaces include the induction and recursion developments in `chap2`, set
operations and finite-set results in `chap3`, integer/rational arithmetic in
`chap4`, the construction of the real numbers in `chap5`, sequential limits
and limsup/liminf in `chap6`, series in `chap7`, and infinite/countable-set
interfaces in `chap8`, limits, continuity, compactness, and equivalent
sequences in `chap9`, differentiation in `chap10`, and Riemann and
Riemann--Stieltjes integration in `chap11`. Appendix A contains the formal
logic and proof-language examples.

Verify the final registered chapter under its configured prefix with:

```text
target/release/litex -graph -f scripts/Analysis/textbook/chapter11-riemann-integral.lit
```

The historical full-book README and comment-only `todo.lit` ledger remain in
`todo_textbook_chapters/`; they are not executable chapters. For the Chapter
11 recovery, the explicitly selected acceptance boundary is the registered
chapter `-f`; no source or formal module `-r` was run.
