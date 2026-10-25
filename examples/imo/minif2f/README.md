# Existing miniF2F IMO proof variants

Nine trust-free proof files for eight IMO problem IDs, copied unchanged from
the local miniF2F `finished` directory. That directory name is historical;
current acceptance is reported below. Dataset statements can cover only a
necessary condition, one part, or an ordered case of an official problem.

| IMO problem | Exact formalized scope | Current check, 2026-10-25 |
| --- | --- | --- |
| [1959 P1](imo_1959_p1.lit) | For positive natural `n`, `gcd(21*n+4,14*n+3)=1`. | Needs migration: goal well-definedness for `21*n+4 != 0`. |
| [1960 P2](imo_1960_p2.lit) | The radical inequality implies `-1/2 <= x < 45/8`, with root and denominator conditions assumed. Does not prove sufficiency. | Needs migration: `s != 1`. |
| [1961 P1](imo_1961_p1.lit) | Positive distinct solutions imply `0 < a` and `b^2 < a^2 < 3*b^2`. Does not construct all solutions. | Needs migration: positivity of the sum of squared differences. |
| [1962 P2](imo_1962_p2.lit) | The stated radical inequality implies `-1 <= x < 1-sqrt(31)/8`. Does not prove sufficiency. | Needs migration: order transport in the radical estimate. |
| [1964 P1, part 1](imo_1964_p1_1.lit) | `7` dividing `2^n-1` implies `3` dividing `n`. | Needs migration: unique integer quotient construction. |
| [1964 P1, part 2](imo_1964_p1_2.lit) | `7` never divides `2^n+1` for natural `n`. | Needs migration: the same quotient construction. |
| [1964 P2](imo_1964_p2.lit) | Triangle-side cubic inequality, with strict positivity and all triangle inequalities. | Strict pass. |
| [1966 P5](imo_1966_p5.lit) | Necessary solution values for the absolute-difference system when `a(1)>a(2)>a(3)>a(4)`. Does not prove all orderings or existence. | Needs migration: substituting absolute differences into the equations. |
| [1973 P3](imo_1973_p3.lit) | A real root of `x^4+a*x^3+b*x^2+a*x+1` implies `a^2+b^2 >= 4/5`. Does not prove attainment of the minimum. | Strict pass. |

Each source is standalone and uses no external module. Run a file from the
repository root, for example:

```sh
target/release/litex -lang en -strict -f examples/imo/minif2f/imo_1964_p2.lit
```

Thirty other official-IMO-named files in that local `finished` directory
contain active `trust` statements and are excluded from the completed-proof
collection. The 2007 shortlist file is also an assumed result and is excluded.
The complete, explicit 1983 P6 and 2006 P3 developments are already in
[inequalities](../inequalities/README.md), rather than their assumed miniF2F versions.

The organization task preserves these nine source files and reports the seven
current failures without repairing their proofs or changing the kernel.
See [verification.md](../verification.md) and the [combined index](../README.md).
