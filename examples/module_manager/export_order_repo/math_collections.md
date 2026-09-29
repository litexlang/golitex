# Mathematical Collections

This module models a minimal dependency chain rather than a substantial
mathematical theory. Its important concept is an exported value whose proof
context is assembled from earlier files and submodules.

`A::chap2::x` is a checked real object equal to `1`. `A::chap3::z` depends on
that qualified object. The root selection tracer defines
`explicit_export_selection::explicit_export_selection_witness`, and
`main.lit` consumes `A::chap3::z` before defining `answer`.

The ideal Litex shape is the implemented ordered export interface:

```litex
have x R = 1
A::chap2::x = 1
have z R = 1
A::chap3::z = 1
have explicit_export_selection_witness R = 1
have answer R = 1
```

The nearest rejected shape is citing `A::chap3::z` from a file ordered before
`A`, because the defining submodule has not loaded yet. The module has no proof,
existence, uniqueness, or well-definedness holes.
