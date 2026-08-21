# Analysis I: current runnable module

This is the current release-verified subset of the Analysis I translation. It
exports the project introduction, Chapters 1--7, and Appendix A in the original
namespace order. Chapters 8--11 are preserved in
`../todo_textbook_chapters/` until they and their dependency chain pass the
current release verifier again.

The runnable module currently covers introductory mathematical language,
natural numbers, set theory, integers, and rationals. Representative public
interfaces include the induction and recursion developments in `chap2`, set
operations and finite-set results in `chap3`, integer/rational arithmetic in
`chap4`, the construction of the real numbers in `chap5`, sequential limits
and limsup/liminf in `chap6`, and series in `chap7`. Appendix A
contains the formal logic and proof-language examples.

Run the complete current module with:

```text
target/release/litex -compact -runner -r scripts/Analysis/textbook
```

The historical full-book README and every quarantined chapter remain beside
the source workspace in `todo_textbook_chapters/`; their presence is not a
current publication or verification claim.
