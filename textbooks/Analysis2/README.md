# Analysis II: runnable entrypoint only

The current release-verified module contains only `Introduction.lit`. Every
mathematical chapter is preserved in `../todo_textbook_chapters/`: Chapter 1
fails its current registered-file gate, Chapter 4 exceeds the publication
timeout, and the remaining chapters depend on quarantined earlier namespaces.

This directory is therefore a runnable project entrypoint, not a published
formalization of Analysis II mathematics yet.

```text
target/release/litex -compact -runner -r scripts/Analysis2/textbook
```

The previous full-module README is preserved under
`../todo_textbook_chapters/README.previous-module.md`.
