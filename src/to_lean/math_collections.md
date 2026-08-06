# Rational-Expression Translation Model

## Recursive fraction pair

The experiment maps a supported real expression `e` to a pair `(p, q)` meaning
`e = p / q`. This pair is structural rather than a human-minimal printed form.
Lean performs the final polynomial normalization and equality check.

Representative rules:

```text
atom a       -> (a, 1)
u + v        -> (pu * qv + pv * qu, qu * qv)
u - v        -> (pu * qv - pv * qu, qu * qv)
u * v        -> (pu * pv, qu * qv)
u / v        -> (pu * qv, qu * pv)
u ^ n        -> (pu ^ n, qu ^ n) for literal n in N
```

This matters because one recursive walk both renders the original Lean
expression and exposes whether denominator clearing is required. Polynomial
equalities use `ring`; remaining denominators use `field_simp` with the
translated explicit nonzero premises and then `ring`.

## Chained division

Division is left-associative in the Litex parser. Consequently,
`1 / 2 / 3 / 4` reaches this model as `(((1 / 2) / 3) / 4)`, and the recursive
rule accumulates the pair `(1, (2 * 3) * 4)`. This is intentionally a structural
normal form rather than a reduced numeric fraction. For a closed numeric
equality such as `1 / 2 / 3 / 4 = 1 / 24`, Lean's `norm_num` checks that the
two recursively built forms denote the same real number.

## Boundary

The ideal later interface could normalize numerator and denominator polynomials
inside Litex and carry proof evidence for every denominator. This experiment
does neither. Its nearest rejected forms are a nonliteral exponent, a
non-rational object such as `sin(x)`, or a denominator whose nonzero evidence is
only implicit rather than an explicit universal premise.
