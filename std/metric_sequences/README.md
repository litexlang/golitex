# Metric sequences and the Banach fixed-point theorem

This module adds metric sequence limits, Cauchy sequences, completeness and
contraction iteration, with 30 named source theorems. It imports `metric` and
`real_series`; the existing metric module retains its original dependencies.

The checked real-line example is f(x)=x/2+1 with start 0. Its iterates are
u(0)=0, u(1)=1, u(2)=3/2 and u(3)=7/4. Banach gives a unique fixed point,
the selected value is 2, the orbit converges to 2 and the step-three distance
is 1/4. The full caller is [validation/main.lit](validation/main.lit).

## Interfaces

| Interface | Mathematical contract |
| --- | --- |
| `has_metric_limit(A,M,a,p)` | Every positive-radius ball at p contains an entire eventual tail of a:N+ -> M.carrier. |
| `is_metric_cauchy_tail(A,M,a,epsilon,cutoff)` | Both indices at least the positive cutoff have distance less than positive epsilon. |
| `is_metric_cauchy(A,M,a)` | Such a cutoff exists for every positive epsilon. |
| `is_complete_metric_space(A,M)` | Every metric Cauchy sequence has a limit in the actual carrier. Empty carriers are allowed. |
| `is_contraction_map(A,M,f)` | Some real q with 0 <= q < 1 makes f a Lipschitz self-map. |
| `iterate<S,f,start>(n)` | Actual recursive iteration on n in N, with u(0)=start and u(n+1)=f(u(n)). |
| `orbit_sequence<S,f,start>(k)` | The same iterates at k in N+, starting with u(1); u(0) is separate. |
| `shifted_sequence<S,a,offset>(k)` | Actual a(k+offset), with nonnegative integer offset. |
| `real_line_metric` | The constructed metric with carrier R and distance abs(x-y); `real_line_metric_components()` exposes its fields. |
| `contraction_fixed_point<A,M>(f)` | Actual uniquely determined point, guarded by completeness, nonemptiness and contraction. |

Template applications use a leading backslash, for example
`\s::iterate<S,f,start>(n)`. Import with an explicit module alias:

```toml
[import std]
Metric = metric
Sequences = metric_sequences
[alias]
m = Metric::main
s = Sequences::main
```

After checking `affine` and its contraction hypothesis on the constructed real
line, the checked caller uses:

```litex
release thm s::real_line_metric_is_complete()
release thm s::banach_fixed_point(R,s::real_line_metric,affine)
release thm s::contraction_fixed_point_value(R,s::real_line_metric,affine,2)
\s::contraction_fixed_point<R,s::real_line_metric>(affine)=2
```

This is an in-context excerpt; the full caller releases the real-line fields,
proves the Lipschitz factor 1/2, checks nonemptiness and proves affine(2)=2.
Imports expose declarations rather than merging their ambient facts. Explicit
point-carrier and real-valued intermediate facts remain valid proof steps;
the consumer records the setup needed by theorem-goal storage.

## Theorems and estimates

Limits are unique, constant sequences converge and convergence implies Cauchy.
Pointwise equality, integer shifts and continuous/Lipschitz images preserve
limits. On the constructed real line, metric and native real limits agree;
metric Cauchy implies native Cauchy, giving real-line completeness.

For u(n)=f^n(start), D=d(start,f(start)) and 0 <= q < 1, the source proves
adjacent, finite-gap and tail estimates, the Cauchy property and convergence
to the unique fixed point p in a nonempty complete metric space. In particular:

- d(u(n),u(n+1)) <= q^n D.
- d(u(n),u(n+k)) <= (q^n-q^(n+k)) D/(1-q).
- d(x,p) <= d(x,f(x))/(1-q).
- d(u(n),p) <= q^n d(start,p) <= q^n D/(1-q).
- d(f(x),p) <= q d(x,f(x))/(1-q).

The error estimates apply to a supplied fixed point without completeness.
The existence theorem assumes no fixed point, limit, Cauchy orbit or geometric
bound as an extra premise. The zero factor is supported, including n=0 with
q^0=1; constant maps reach their fixed point after one step.

## Verification and boundaries

Run `python3 std/metric_sequences/validation/check.py` from the repository root.
The strict source contains 45 accepted statements. The full imported consumer
contains 106 accepted statements, including generic callers for all 30 theorems,
the affine example, the zero-factor constant map, the empty complete metric
space with no fixed point and the noncontractive 1-Lipschitz real identity.
Twelve final-statement controls cover missing assumptions and illegal domains;
the checker first replays the same fully accepted consumer into the negative Session.

Generated metric topology, closed-subspace completeness, products, compactness,
completions and normed/Banach spaces remain later work. This module provides
the contraction theorem, not all functional analysis. Native real-sequence
`lim` has no new overload. No native code, trust or new axiom is added.
See [math_collections.md](math_collections.md) for the dependency spine.
