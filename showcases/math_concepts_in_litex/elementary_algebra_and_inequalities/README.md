# Elementary Algebra and Inequalities

This independent first version checks a short, recognizable algebra spine:

- two-variable AM-GM for nonnegative reals, consumed at `9, 16`;
- a general nondegenerate linear-equation solver;
- the real quadratic formula for a nonzero leading coefficient and
  nonnegative discriminant; and
- the radical equation `x = sqrt(11 - 2*x) + 4`, with the square-root domain
  stated explicitly, the quadratic formula applied at `(1, -6, 5)`, and the
  extraneous root rejected.

Run it from the repository root with:

```bash
target/release/litex -compact -runner -r showcases/math_concepts_in_litex/elementary_algebra_and_inequalities
```

The file uses Builtin real arithmetic, order, powers, and square root. It
contains no `trust` or local axiom. It exposes the standard real quadratic
formula under a nonnegative discriminant, not a general polynomial solver.

`same_math_in_lean.lean` covers the same AM-GM and radical-candidate spine with
Prelude integers. It keeps the factorized candidate argument rather than the
real quadratic formula, and exposes the square/order step behind AM-GM as an
explicit premise because Prelude has no real square root. It has no imports
and is handwritten comparison code, not compiler-generated output. Run it
with:

```sh
lean showcases/math_concepts_in_litex/elementary_algebra_and_inequalities/same_math_in_lean.lean
```
