# Linear Algebra Done Right: current runnable module

The current release-verified module contains the introduction and Chapters 1A
and 1B. It develops the scalar-system interface, real and complex scalar
adapters, finite-list/vector vocabulary, and the first vector-space structures.

Chapter 1C and all later chapters remain in `../todo_textbook_chapters/`.
Some fail their own current registered-file gate; others pass in a trusted old
prefix but directly depend on one of those quarantined namespaces, so they are
not a coherent publication without the missing earlier layer.

```text
target/release/litex -compact -runner -r scripts/linear_algebra_done_right/textbook
```

The previous full-module README is preserved beside the quarantined files.
