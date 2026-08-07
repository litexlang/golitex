# Internal Example Material

This directory keeps developer-facing material out of the public example
reading path.

- `regression/` contains stable, descriptively named verifier regressions.
- `fixtures/` contains configured modules or data used by another example or
  test. A fixture is not a standalone tutorial.
- `drafts/` contains exploratory Litex developments whose names state the
  mathematical or diagnostic topic instead of using `tmp*` names.
- `to_lean/` contains inputs used while developing generated Lean output.
- `proof_journals/` preserves proof-attempt evidence associated with example
  work; it is not input to the Litex runner.

The release examples harness still syntax- and verification-checks `.lit`
files under this directory unless a more specific runner owns the artifact.
Public documentation should link to a reader-facing example whenever one
exists.
