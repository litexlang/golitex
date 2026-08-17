# Internal Example Material

This directory keeps developer-facing material out of the public example
reading path.

- `regression/` contains stable, descriptively named verifier regressions.
- `fixtures/` contains configured modules or data used by another example or
  test. A fixture is not a standalone tutorial.
- `drafts/` contains exploratory Litex developments whose names state the
  mathematical or diagnostic topic instead of using `tmp*` names.
- Litex-to-Lean compiler tracers live as generated `.lit`/`.lean` pairs under
  `lean/examples/`.

These files support implementation and regression coverage; they are not part
of the public reading path.
