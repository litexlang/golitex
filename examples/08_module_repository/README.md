# Repository Module Example

This configured project demonstrates ordered exports, submodules, and
cross-file qualified names.

The root `litex.config` exports submodule `A` before `main.lit`.
`A/litex.config` exports `chap2.lit`, `chap3.lit`, and `main.lit` in order, so
`chap3.lit` can cite `A::chap2::x` directly.

After `A` has loaded, `main.lit` checks `A::chap3::z = 1` through its canonical
qualified name. Cross-module references always retain the module/export path.

Selecting submodule `A` traces back to the root module, evaluates everything
before `A`, and then evaluates all of `A`. Selecting an exported file follows
the same recursive prefix order through that file.

The public result is `answer`, a checked real object equal to `1`. The example
contains no `trust`, axiom, or abstract proposition boundary.
