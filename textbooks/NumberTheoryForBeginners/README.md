# Number Theory for Beginners

This Litex project translates the non-exercise mathematical development of
André Weil and Maxwell Rosenlicht's *Number Theory for Beginners* in source
order. Run it from the repository root with:

```sh
RUST_MIN_STACK=8388608 target/debug/litex -compact -runner -r textbooks/NumberTheoryForBeginners
```

The project exports Sections I–XIII. Its checked public surface includes
integer divisibility and Euclidean division, gcd and Bézout interfaces,
relative primality, congruences and residue classes, elementary group
interfaces, a finite-support polynomial carrier with sum, convolution, degree,
division, gcd, and ideal interfaces, power congruences, the Legendre-symbol
specification, and concrete Gaussian-integer coordinate operations.

The current trust boundary is explicit in `todo.lit`. It is concentrated in
finite quotient/counting arguments, finite cyclic groups, generic polynomial
Euclidean theory, finite-field power maps, quadratic reciprocity, and Gaussian
Euclidean factorization. The project currently contains no `abstract_prop`.

A representative use is the checked Euclidean division interface:

```litex
by thm section2::euclidean_division_exists(a, d)
obtain q, r from exist q, r Z st {section2::euclidean_division_Z(a, d, q, r)}
```

`math_collections.md` explains the intended mathematical interfaces and their
dependency order. `todo.lit` is a comment-only ledger and is not exported.
