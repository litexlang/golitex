# Reusable Mathematics Policy

Litex does not preload a mathematical standard library during runtime
construction. Bundled standard modules such as `basics` load only when a
top-level `litex.config` lists them under `[import std]`. Other non-kernel
background mathematics belongs in a project or source-local cite dependency,
whose names remain explicitly qualified. The old experimental collection under

## Where a fact belongs

1. Keep a fact in the source file when it is only needed there.
2. Put supporting background in that source's adjacent cite package when the
   proof is routine, unfinished, or would obscure the source's main line. A
   cite package must name every fact it exposes and make every `trust` boundary
   visible.
3. Add a kernel primitive or verifier builtin only when the fact is a small,
   stable part of Litex's mathematical meaning or verification model. A kernel
   builtin is not a shortcut for unproved ordinary mathematics; other facts
   belong in an explicit source-local or project package instead.

## Sharing a fact

A fully proved fact may become part of a reusable project package only after
all of the following are true:

- its statement is fully checkable, with no `trust` in its proof path;
- at least three independent source families use the same stable interface;
- the package has a focused verification test and clear source provenance;
- importing it stays explicit through the project's `litex.config`; no
  mathematical package is loaded automatically.

Until then, duplicate only the small interface that a source needs, or keep a
source-local cite package. Translation work should treat a missing fact as
evidence about the current source, package design, or kernel—not as a reason to
restore a global mathematical environment.

No exception carries trusted mathematical theory globally. A core primitive
must be a small semantic interface, such as the Euclidean
`integer_quotient(a, d)` paired with `%`; every ordinary theorem, including
Archimedean, rational-density, reduced-fraction, power, and extrema facts,
keeps an explicit source-owned proof or `trust` boundary.
