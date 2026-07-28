# Construct Selection Cases

Use these examples to distinguish a definition that merely states a condition
from one that introduces an interface later code must use.

## 1. A relation stays a `prop`

An epsilon-closeness predicate says whether a chosen pair is close. It does not
introduce a new value:

```litex
prop is_close_in_Q(epsilon Q_pos, x, y Q):
    dist_Q(x, y) <= epsilon
```

Later code asserts `$is_close_in_Q(epsilon, x, y)`. It never applies
`is_close_in_Q` as a map.

Do not create a function merely because a definition has parameters.

## 2. A formula that must be applied is `have fn`

Rational distance is a named map used in later expressions:

```litex
have fn dist_Q(x, y Q) Q = abs(x - y)

dist_Q(1, 3) = 2
```

The bad fallback is a relation such as
`prop is_rational_distance(x, y, d)`. That forces every later line to carry
an extra `d` and an equality instead of writing `dist_Q(x, y)`.

## 2a. A set-valued formula is still `have fn`

The notation (m\mathbb Z) introduces a set for each integer `m`, so its
Litex interface is a function from `Z` to `power_set(Z)`. Its mathematical
meaning is:

```text
mZ(m) = {x Z: exist k Z st {x = m * k}}
```

The current parser does not accept that existential body directly inside a
set-builder. Keep the intended `have fn` boundary, expose the existence
condition as a relation, and use the currently checkable surface:

```litex
prop divides_Z(a, b Z):
    exist k Z st {b = a * k}

have fn mZ(m Z) power_set(Z) = {x Z: $divides_Z(m, x)}

6 $in mZ(3)
-6 $in mZ(3)
```

The direct existential version is therefore mathematically correct but
currently `blocked` by the parser; it must not be silently replaced by a
`prop` declaration for `mZ` itself.

Do not replace `mZ` with only `prop is_multiple(m, S)`: that describes a
condition on a proposed set but does not let later code apply `mZ(m)`. Also
reject the tempting but ill-typed or unrelated body
`{x power_set(Z): forall! k Z: x % k = 0}`: `x` is then a subset of `Z`, `m`
does not occur, and `forall!` expresses a universal remainder condition rather
than the witness equation `x = m * k`.

If the source restricts `m` to a nonzero domain where remainder is defined, the
equivalent surface `{x Z: x % m = 0}` may be useful. It is not a reason to
silently change a `m Z` interface to `m N`.

## Function restrictions are values, not compatibility facts

When a property expects a function on a particular domain, make that domain
part of its parameter type:

```litex
prop p(f fn(x Z) Z):
    forall x Z:
        f(x) = f(x)
```

If `g` is defined on a larger domain, pass the ordinary restricted function
value explicitly:

```litex
$p(fn(x Z) Z {g(x)})
```

Treat this as the Litex spelling of `g | Z`. Do not introduce a separate
restriction `prop` or use a compatibility predicate that silently changes the
domain of `g`; a smaller-domain function must be visibly constructed where it
is passed.

## 3. A uniquely determined value is `have fn by exist!`

The epsilon-delta relation is correctly a property of a candidate derivative:

```litex
prop has_derivative_at(X power_set(R), f fn(x X) R, x0 X, L R):
    ...
```

After existence and uniqueness are available, expose the selected value as a
function:

```litex
have fn derivative by exist!:
    ? forall X power_set(R), f fn(x X) R, x0 X:
        $is_differentiable_at(X, f, x0)
        =>:
            exist! L R st {$has_derivative_at(X, f, x0, L)}
    ...
```

The downstream probe must apply `derivative(X, f, x0)` and relate it back to
`$has_derivative_at(X, f, x0, derivative(X, f, x0))`. Do not leave the
derivative only as an existential `prop` when later theorems need its value.

If the unique-existence proof is unavailable, report `blocked` with that
missing obligation; do not invent a `prop derivative(...)` replacement.

## 4. A parameterized declaration family is `template`

A sequence type whose lower index and codomain vary with parameters is an
instantiable declaration, not a condition:

```litex
template<s set, m N_pos>:
    have seq_starting_at set = fn(x N_pos: x >= m) s

have a_from_3 \seq_starting_at<N, 3>
```

The use probe is the instantiation `\seq_starting_at<N, 3>`. A predicate
such as `prop is_sequence_starting_at(a, s, m)` may describe membership in a
particular sequence space, but cannot generate the reusable type needed by
callers.

## Fast rejection questions

Ask these before accepting a `prop` translation:

1. Will a later line need `f(x)`, a named value, or an instantiated
   `\template<...>`? If yes, do not use only `prop`.
2. Does the source say “define”, “let”, “the function”, “the unique value”, or
   “for each parameters introduce”? If yes, start from a construction form.
3. Can the candidate be used after its definition without inventing a witness
   or equality every time? If no, the interface is probably too weak.

## Source anchors

- `scripts/textbooks_drafts/Analysis/chapter04-integers-and-rationals.lit`:
  `dist_Q` and `is_close_in_Q`.
- `scripts/textbooks_drafts/Analysis/chapter10-differentiation.lit`:
  `derivative` from unique existence.
- `scripts/textbooks_drafts/Analysis/chapter05-real-numbers.lit`:
  `seq_starting_at` template.
