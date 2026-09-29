# Repository Module Example

This configured project demonstrates ordered exports, submodules, and
cross-file qualified names.

The root `litex.config` exports submodule `A`,
`explicit_export_selection.lit`, and then `main.lit`.
`A/litex.config` exports `chap2.lit`, `chap3.lit`, and `main.lit` in order, so
`chap3.lit` can cite `A::chap2::x` directly.

The manifest is an explicit selection list. `unlisted_sidecar.lit` and the
`notes/` directory remain beside it but do not enter discovery, execution, or
the module namespace. The exported tracer checks that namespace boundary in a
transactional `try` block, so a successful module run demonstrates that only
declared exports were selected while every standalone example remains valid.

After `A` has loaded, `main.lit` checks `A::chap3::z = 1` through its canonical
qualified name. Cross-module references always retain the module/export path.

Selecting submodule `A` traces back to the root module, evaluates everything
before `A`, and then evaluates all of `A`. Selecting an exported file follows
the same recursive prefix order through that file.

The public results include `explicit_export_selection_witness` and `answer`,
both checked real objects equal to `1`. The exported example contains no
`trust`, axiom, or abstract proposition boundary.
