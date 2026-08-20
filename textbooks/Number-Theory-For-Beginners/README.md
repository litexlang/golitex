# Number Theory for Beginners: runnable entrypoint only

The current release-verified module contains only `Introduction.lit`. The
section files and finite-product toolkit are preserved in
`../todo_textbook_chapters/`: most fail their current registered-file gate, and
the two individually green mathematical files still require quarantined
`section2` or `section5` interfaces.

```text
target/release/litex -compact -runner -r scripts/number_theory_for_beginners/textbook
```

This is a runnable entrypoint, not a current publication of the book's
mathematical sections. The previous module README remains with the quarantined
files.
