# Real closed-interval existence laws

This module proves the intermediate value theorem from native real completeness
and pointwise relative continuity. Seven named source theorems cover local upper bounds, bounded continuous
images on closed intervals, strict
and weak endpoint inequalities, either endpoint-value order, and an interior
point for a strict intermediate value. A singleton interval is allowed in the
weak theorem. No monotonicity or uniqueness is assumed or concluded.

## Import and an actual zero

Use a caller manifest with its own export:

```ini
[import std]
Intervals = real_interval_laws
[alias]
intervals = Intervals::main
[export]
main = "./main.lit"
```

This complete caller example proves that
x^3-x-1 has a zero strictly between 1 and 2:

```litex
have fn cubic(x '[1,2]) R=x^3-x-1

forall x '[1,2]:
    $is_continuous_at(cubic,x)

cubic(1)=-1

cubic(2)=5

release thm intervals::interval_intermediate_value_interior(1,2,cubic,0)

obtain cubic_root from exist x '[1,2] st {1<x,x<2,cubic(x)=0}

cubic_root^3-cubic_root-1=cubic(cubic_root)=0
```

The function's complete domain is the closed interval. For a function defined
on a larger domain, construct its actual restriction with
`fn(x '[a,b]) R {f(x)}`; the original function is not retyped. Continuity is
relative to that complete domain, so the endpoint condition is the appropriate
one-sided continuity and the singleton case has its usual meaning.

## Public theorems

Every intermediate-value theorem takes a, b, f, level, with a real and b in {t in R:t>=a}, and
f a complete real-valued function on [a,b]. Every point of that interval must
satisfy the native `is_continuous_at` relation.

| Theorem after `intervals::` | Additional premises and conclusion |
| --- | --- |
| `interval_intermediate_value_strict` | f(a)<level<f(b); an actual c in [a,b] has f(c)=level. |
| `interval_intermediate_value_ordered` | f(a)<=level<=f(b); includes either endpoint and a=b. |
| `interval_intermediate_value` | min(f(a),f(b))<=level<=max(f(a),f(b)); either endpoint-value order. |
| `interval_intermediate_value_interior` | Strict inequalities against that minimum and maximum; supplies c in [a,b] with a<c<b and f(c)=level. |

The result is existential. A constant function can have many points attaining
the value; there is no selected or unique root interface.

The additional bound theorems have separate fixed signatures:

| Theorem after `intervals::` | Contract |
| --- | --- |
| `continuous_real_function_local_upper_bound(D,f,p)` | Relative continuity at p in the actual real domain D gives a positive-radius neighborhood on which f(x)<f(p)+1. The complete domain need not be an interval. |
| `interval_continuous_image_bounded_above(a,b,f)` | Pointwise continuity on the actual closed interval gives a real upper bound for the whole image. |
| `interval_continuous_image_bounded(a,b,f)` | The same hypotheses give both real image bounds. These bounds need not be optimal or attained. |


## Verification and scope

Before the user's pause and cleanup request, the focused gates checked eight
strict source statements, 75 independent imported
statements, the separate seven-statement README example, and ten final-only
refusals after replaying all 75 positives in a fresh Session. All seven theorem
contracts were exercised at their full domains. Concrete uses included both
endpoint orders, endpoints, a singleton, a constant function with two distinct
zero witnesses, extracted cubic image bounds, and OpenStax Calculus 1 section 2.4, Checkpoint 2.26.

Refusals covered an outside value, a discontinuous sign function, a wider
complete function domain, an endpoint in the strict interior theorem, a wrong
singleton value, false uniqueness, reversed interval arguments, and invalid
closed-image/local-point bounds. An endpoint reciprocal is separately proved
unbounded on [0,1], so dropping continuity has a genuine counterexample.
All acceptance fixtures, the checker, local journals and the pinned executable
were then removed at the user's request. These counts describe the historical
checkpoint; no test suite or raw receipt is retained for this increment. The
underlying real arithmetic, completeness and continuity rules remain part of
Litex's native foundation. There is no source trust, user axiom or kernel
change, and no Lean replay is claimed.

Attained extrema, uniform continuity, compactness
bridges and the mean-value/Taylor progression remain to be implemented or
accepted separately. This module supplies the intermediate-value and bounded-image
part of the continuity chapter.
See [math_collections.md](math_collections.md) for the proof dependencies.
