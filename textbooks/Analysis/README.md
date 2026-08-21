# Analysis I: current runnable module

This is the current release-verified subset of the Analysis I translation. It
exports the project introduction, Chapters 1--10, and Appendix A in the
original namespace order. Chapters 8--10 have passed persistent source-order
replay and their registered canonical `-f` gates with exit 0 and top-level
`ok=true`. The synchronized formal mirror passes the same registered-file
boundary. Chapter 11 is preserved in `../todo_textbook_chapters/` until it
passes the current release verifier again.

The runnable module currently covers introductory mathematical language,
natural numbers, set theory, integers, and rationals. Representative public
interfaces include the induction and recursion developments in `chap2`, set
operations and finite-set results in `chap3`, integer/rational arithmetic in
`chap4`, the construction of the real numbers in `chap5`, sequential limits
and limsup/liminf in `chap6`, series in `chap7`, and infinite/countable-set
interfaces in `chap8`, limits, continuity, compactness, and equivalent
sequences in `chap9`, and differentiation in `chap10`. Appendix A contains the
formal logic and proof-language examples.

Run the complete current module with:

```text
target/release/litex -compact -runner -r scripts/Analysis/textbook
```

The historical full-book README and Chapter 11 remain beside the source
workspace in `todo_textbook_chapters/`; their presence is not a current
publication or verification claim. For the Chapter 10 recovery, the explicitly
selected acceptance boundary is the registered chapter `-f`; no source or
formal module `-r` is required.
