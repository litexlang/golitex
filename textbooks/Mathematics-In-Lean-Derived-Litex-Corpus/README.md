# Mathematics in Litex: current runnable module

This release-verified subset exports the introduction and Chapters 1, 3, 5, 6,
and 7. It includes introductory functions and bounds, propositional logic,
elementary number theory, discrete mathematics, and reusable algebraic
structures. The alternative structured-basics submodule remains an explicit
import.

Chapters 2, 4, and 8--12 fail their current registered-file gates. Chapter 13
passes only when the quarantined Chapter 12 namespace is trusted, so it is also
preserved under `../todo_textbook_chapters/` rather than published as a
coherent chapter.

```text
target/release/litex -compact -runner -r scripts/mathematics_in_litex/textbook
```

The previous full-corpus README is preserved with the quarantined chapters.
