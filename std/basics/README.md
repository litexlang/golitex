# `std/basics`

`std/basics` is an empty compatibility module. Its directory,
`litex.config`, and `main.lit` remain packaged so this stays valid:

```litex
import std basics
```

The import exports no names. Use native Litex vocabulary directly, including
`quot(a, d)`, `$dvd(x, d)`, `gcd(a, b)`, `lcm(a, b)`, `$prime(p)`,
and the bare reserved theorem `rational_has_unique_reduced_fraction(q)`.

A development that needs a theorem not supplied by the kernel should define
and prove it in its own module. In particular, textbook-facing Euclidean and
Bezout interfaces now live with the textbooks that use them.
