# LaTeX conversion fixtures

These are parse-only fixtures, not positive verification examples.
`project/beta.lit` intentionally contains a false equality and references
same-named members in two different dependency namespaces. One dependency has
invalid Litex syntax and the other contains a false fact. Their manifests are
valid: conversion must mount naming metadata without running dependency source.

The dedicated positive verification/conversion tracer and Chinese document
are under `examples/stmt_nodes/compile_to_latex/`.

`command_separation_acceptance.json` records the 2026-10-07 release checks for
the independent executable extraction and LaTeX launch commands: 50 focused
tests, 22 unchanged baseline artifact envelopes, direct tracer verification,
and the false-fact boundary between parse-only conversion and verified code
extraction. The original `acceptance.json` retains the native typography checks.
