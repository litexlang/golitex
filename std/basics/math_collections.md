# Mathematical design of `std/basics`

This module intentionally has no mathematical nodes and no exported
declarations. It is retained only as an import-compatible package skeleton.

Former source wrappers were migrated as follows:

- Euclidean quotient selection uses native `quot(a, d)`.
- Integer divisibility uses native dividend-first `$dvd(x, d)`.
- gcd, lcm, prime, coprime, exp, ln, sign, factorial, finite-set extrema, and
  reduced rational normalization use their native objects, predicates, or
  reserved bare theorems.
- Euclidean-algorithm, Bezout, and other source-facing theorem suites that are
  not kernel interfaces are defined and proved in the local textbook or
  example that needs them.

The boundary is deliberate: importing `std/basics` succeeds, but qualifying
any former declaration with `basics::` does not.
