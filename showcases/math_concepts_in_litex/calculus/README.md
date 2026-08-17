# Single-Variable Real Calculus

This independent first version implements a checked derivative tranche:

- an epsilon-delta control relation for a proposed derivative value;
- `has_derivative_at_R` as the corresponding candidate-value predicate;
- the real square function;
- cancellation of its punctured difference quotient; and
- a proof that the square function has derivative candidate `2*x0` at every
  real `x0`, consumed concretely at `x0=3` to obtain `6`;
- a parameterized affine-function family whose derivative is its slope;
- differentiability as existence of a derivative candidate, with reusable
  introduction theorems and concrete consumption for `3*x+2`; and
- the tangent to `x^2` at `3`, whose exact remainder is `(x-3)^2`.

Run it from the repository root with:

```bash
target/release/litex -compact -runner -r scratch/math_concepts_in_litex/calculus
```

The executable file contains no `trust` or local axiom. Derivatives remain a
relation with a proposed value: uniqueness and a selected derivative function
are not assumed. General limits and continuity, compact-interval theorems, the
Mean Value Theorem, Riemann integration, and the Fundamental Theorem of
Calculus remain later gates, not current API claims.

For comparison, `lean_core_analogy.lean` checks the same epsilon-delta witness
shape using only Lean's automatically loaded Prelude. Because Prelude has no
real-number or ordered-field library, the real operations and two algebraic
identities consumed by the proof are explicit setting fields. The file is a
handwritten semantic analogy, not compiler-generated output. Run it with:

```sh
lean showcases/math_concepts_in_litex/calculus/lean_core_analogy.lean
```
