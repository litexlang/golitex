# To-Lean Translation Model

## Known-forall instantiation

A successful use of a known forall retains four distinct pieces of evidence:

```text
recorded Obj arguments
  -> typed local proof_arg values
  -> recursively proved domain requirements
  -> direct instantiated conclusion
  -> optional checked normalization to the requested goal
```

The parameter-type requirements remain explicit in IR. Lean realizes each one
by type-checking a local definition such as `let proof_arg_2_1 : ℝ := e`; this
is the Lean evidence that the chosen Litex object inhabits the translated
forall binder type. Proposition-valued domain requirements instead become
named `proof_fact` values and are supplied to the cited theorem after the
`proof_arg` values.

The direct conclusion is instantiated from the exact recorded objects. It is
not replaced with the requested goal merely because Litex's matcher accepted
the two. For the current atomic rational slice, a different but rationally
equivalent target is represented by an outer `Normalization` rule. This gives
the inner forall application its own proof space and leaves the outer proof to
check the conversion with `norm_num`, `ring`, or `field_simp` plus `ring`.

The nearest boundary is a direct instance and goal that need some other form of
transport, or a recursively verified domain requirement whose proof rule has no
Lean backend. Both remain explicit unsupported nodes and stop compilation.

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

## Rational-expression boundary

The ideal later interface could normalize numerator and denominator polynomials
inside Litex and carry proof evidence for every denominator. This experiment
does neither. Its nearest rejected forms are a nonliteral exponent, a
non-rational object such as `sin(x)`, or a denominator whose nonzero evidence is
only implicit rather than an explicit universal premise.
