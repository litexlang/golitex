# Real Riemann integral laws

This source-only module proves absolute-value bounds for finite real Riemann
integrals. It adds six ordinary source theorems and no native object, fact,
builtin theorem, strategy or automatic integrability search. All functions
have the supplied complete domain `D`, a subset of R, covering the closed
interval between the endpoints.

Import in `litex.config`:

```ini
[import std]
integrals = real_integral_laws
[alias]
integrals = integrals::main
```

For `f,g : D -> R`, real candidates `I,J`, and real endpoints `a,b`:

| Call | Contract |
| --- | --- |
| `riemann_integral_absolute_bound(a,b,D,f,g,I,J)` | If `a<=b`, both candidates exist, and `g(x)=abs(f(x))` throughout the interval, then `abs(I)<=J`. |
| `riemann_integral_absolute_bound_oriented(a,b,D,f,g,I,J)` | Under the same candidate and pointwise assumptions for either endpoint order, `abs(I)<=abs(J)`; equal endpoints are allowed. |
| `riemann_absolute_integrable_from_continuous(a,b,D,f,g)` | If `f` is continuous at every interval point and `g(x)=abs(f(x))` throughout D, then `g` is Riemann integrable. |
| `riemann_absolute_bound_continuous(a,b,D,f,g)` | With the same continuity and global pointwise relation, both integrals have finite candidates satisfying the oriented bound. |
| `riemann_integral_difference_bound(a,b,D,f,g,d,h,I,J,K)` | For `a<=b`, candidates I,J,K with `d=f-g`, `h=abs(d)` on the interval give `abs(I-J)<=K`. |
| `riemann_integral_difference_bound_oriented(a,b,D,f,g,d,h,I,J,K)` | With either endpoint order, the corresponding conclusion is `abs(I-J)<=abs(K)`. |

Every theorem requires the closed sorted interval to be a subset of D. The
candidate-bound theorems require their pointwise relations only on that interval; the
continuity theorems require it throughout D to establish relative continuity
of `g` at the interval points. They do not establish integrability of `abs(f)`
from arbitrary Riemann integrability of `f`: that general theorem remains open.
The bound compares candidates; it does not evaluate either integral.

The [imported example](../../examples/real_analysis/integral_absolute_bound/main.lit)
checks `f(x)=-x` on `[0,1]`, reversed and equal endpoints, and a function
defined only on the actual interval. Run its strict positive and rejection
controls with:

```bash
python3 examples/real_analysis/integral_absolute_bound/check.py
```
