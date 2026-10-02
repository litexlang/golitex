# Repository Module Example

This project imports directory `A`, then runs the root exports
`explicit_export_selection.lit` and `main.lit` in order. `A/litex.config`
exports `chap2.lit`, `chap3.lit`, and `main.lit` in order. Within `A`,
`chap3.lit` cites `chap2::x`; the root cites `A::chap3::z`.

Before migration, the example used `[hierarchy]`, a directory export, and a
transactional `try:` assertion. The current language uses explicit imports,
file-only exports, and a separate executable negative for the unlisted name.
The runnable positive remains in `explicit_export_selection.lit`.

`unlisted_sidecar.lit` and `notes/` remain unexported. From this project
directory, an absolute release binary with
`-strict -e 'unlisted_sidecar::unlisted_sidecar_value = 2'` must reject the
unknown namespace. See the [acceptance commands](../README.md#acceptance).

`-r export_order_repo/A` runs `A` as its own project. `-f` uses the target's
parent config and stops at the selected export; it does not search ancestor
configs. Imports mount before root exports, following the current module
contract. The checked public root results are
`explicit_export_selection_witness` and `answer`, both equal to `1`.
No trust, axiom, or abstract proposition boundary is introduced.
