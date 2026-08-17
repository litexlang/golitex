# Number Theory

This independent first version grows from explicit integer witnesses:

- divisibility and its transitivity law;
- closure of common divisors under integer linear combinations;
- a positive gcd certificate carrying divisor, greatestness, and Bezout data;
- a checked certificate `gcd(84, 30) = 6`, including `6 = 84*(-1) + 30*3`;
- both directions of the linear-Diophantine criterion, followed by the
  solution `84*(-3) + 30*9 = 18`; and
- modular congruence through divisibility, with addition compatibility.

Run it from the repository root with:

```bash
target/release/litex -compact -runner -r scratch/math_concepts_in_litex/number_theory
```

The module has no `trust` or local axiom. Its gcd is a proof-facing
certificate rather than a newly selected global gcd function; a general
Euclidean-algorithm implementation and CRT remain later work.
