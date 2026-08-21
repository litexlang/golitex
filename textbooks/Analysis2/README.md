# Analysis II: runnable textbook prefix

The current release-verified module contains `Introduction.lit` and Chapters
1--3 in source order. Each promoted chapter passes its canonical file gate,
and the cumulative module passes the command below with exit 0 and top-level
`ok: true` on the current release build.

Chapter 4 remains in `../todo_textbook_chapters/` because the current clean
closure stops at `complex_add_real_part` line 552: a directly declared
`&ComplexNumber`-valued result does not yet expose the named `real_part`
projection equality. Chapters 5--8 remain dependency-quarantined behind that
root.

```text
target/release/litex -compact -runner -r scripts/Analysis2/textbook
```

The previous full-module README is preserved under
`../todo_textbook_chapters/README.previous-module.md`; it is historical design
documentation rather than the current export manifest.
