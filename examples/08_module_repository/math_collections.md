# Mathematical Collections

This module models a minimal dependency chain rather than a substantial
mathematical theory. Its important concept is an exported value whose proof
context is assembled from earlier files and submodules.

`A::chap2::x` is a checked real object equal to `1`. `A::chap3::z` depends on
that qualified object, and the root `main.lit` consumes `A::chap3::z` before
defining `answer`.

The ideal Litex shape is the implemented ordered export interface:

```litex
have x R = 1
A::chap2::x = 1
have z R = 1
A::chap3::z = 1
have answer R = 1
```

The nearest rejected shape is citing a later export from an earlier file, or
using an unqualified submodule name that has not been introduced by the
configured hierarchy. The module has no proof, existence, uniqueness, or
well-definedness holes.
