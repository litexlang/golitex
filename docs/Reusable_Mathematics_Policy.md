# Reusable Mathematics Policy

Litex does not distribute or automatically load a mathematical standard
library. The old experimental collection is archived under
`scripts/legacy_std/`; it is not part of a release artifact, import search
path, or CI example suite.

## Where a fact belongs

1. Keep a fact in the source file when it is only needed there.
2. Put supporting background in that source's adjacent cite package when the
   proof is routine, unfinished, or would obscure the source's main line. A
   cite package must name every fact it exposes and make every `trust` boundary
   visible.
3. Add a kernel builtin only when the fact is a small, stable part of Litex's
   mathematical meaning or verification model. A builtin is not a shortcut for
   unproved ordinary mathematics.

## Sharing a fact

A fact may become a reusable project package only after all of the following
are true:

- its statement is fully checkable, with no `trust` in its proof path;
- at least three independent source families use the same stable interface;
- the package has a focused verification test and clear source provenance;
- importing it stays explicit through `litex.config`; no package is searched
  for or loaded automatically.

Until then, duplicate only the small interface that a source needs, or keep a
source-local cite package. Translation work should treat a missing fact as
evidence about the current source, package design, or kernel—not as a reason to
restore a global `std`.
