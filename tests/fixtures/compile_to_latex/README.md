# LaTeX conversion fixtures

These are parse-only fixtures, not positive verification examples.
`project/beta.lit` intentionally contains a false equality and references
same-named members in two different dependency namespaces. One dependency has
invalid Litex syntax and the other contains a false fact. Their manifests are
valid: conversion must mount naming metadata without running dependency source.

The dedicated positive verification/conversion tracer and Chinese document
are under `examples/stmt_nodes/compile_to_latex/`.
