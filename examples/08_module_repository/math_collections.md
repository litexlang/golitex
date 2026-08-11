# Mathematical Collections

This module models a minimal dependency chain rather than a substantial
mathematical theory. Its important concept is an exported value whose proof
context is assembled from earlier files and submodules.

`A::chap2::x` is a checked real object equal to `1`. `A::chap3::z` depends on
that qualified object, and the root `main.lit` consumes the same symbol once as
`A::chap3::z` and once as bare `z` before defining `answer`.

The ideal Litex shape is the implemented ordered export interface:

```litex
have x R = 1
A::chap2::x = 1
have z R = 1
A::chap3::z = 1
z = 1
have answer R = 1
```

The bare spelling is enabled explicitly by `[allow bare export] A`; it is not a
fallback search. The nearest rejected shape is citing `z` from a file ordered
before `A`, creating a local symbol or binder also named `z` after the opt-in is
active, or enabling two public trees with different terminal symbols of the
same name. The module has no proof, existence, uniqueness, or well-definedness
holes.
