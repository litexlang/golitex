# Linear Algebra Done Right: current runnable module

The current release-verified module contains the introduction, Chapters 1A
through 1C, and Chapters 2A through 2C. It develops the scalar-system
interface, real and complex scalar adapters, finite-list/vector vocabulary,
vector spaces, subspaces, finite subspace sums, span, linear independence,
bases, basis extension, finite-dimensional complements, and dimension.

Chapter 2C is runnable but retains nine explicit, localized `trust`
boundaries; this promotion adds no new trust. Chapter 3A and all later chapters
remain in `../todo_textbook_chapters/`.
Some fail their own current registered-file gate; others pass in a trusted old
prefix but directly depend on one of those quarantined namespaces, so they are
not a coherent publication without the missing earlier layer.

```text
target/release/litex -compact -runner -r scripts/linear_algebra_done_right/textbook
```

The previous full-module README is preserved beside the quarantined files.
