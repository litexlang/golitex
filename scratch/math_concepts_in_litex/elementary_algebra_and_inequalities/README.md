# Elementary Algebra and Inequalities

This independent first version checks a short, recognizable algebra spine:

- two-variable AM-GM for nonnegative reals, consumed at `9, 16`;
- a general nondegenerate linear-equation solver;
- the roots of `x^2 - 6*x + 5` by factorization and zero-product cases;
- `abs(x - 3) = 2` by sign cases; and
- the radical equation `x = sqrt(11 - 2*x) + 4`, with the square-root domain
  stated explicitly and the extraneous root rejected.

Run it from the repository root with:

```bash
target/release/litex -compact -runner -r scratch/math_concepts_in_litex/elementary_algebra_and_inequalities
```

The file uses Builtin real arithmetic, order, powers, absolute value, and
square root. It contains no `trust` or local axiom. It is a focused first
version, not a general polynomial solver or a complete inequalities library.
