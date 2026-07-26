# Number Theory for Beginners

This Litex project translates the non-exercise mathematical development of
André Weil and Maxwell Rosenlicht's *Number Theory for Beginners* in source
order. Run it from the repository root with:

```sh
RUST_MIN_STACK=8388608 target/release/litex -compact -runner -r textbooks/NumberTheoryForBeginners
```

The project exports Sections I–XIII directly, with no citation package. Its
checked public surface includes
integer divisibility and Euclidean division, gcd and Bézout interfaces,
the canonical multiple set `mZ(m)` together with its membership
characterization, relative primality, the checked uniqueness of finite
nonnegative group-power sequences, signed-power product and inverse laws, and
zero-exponent law, finite-product prime divisibility and prime-factorization existence,
congruences and residue classes, elementary group interfaces, the finite
residue-class carrier with its exact cardinality, the two-way membership
interface for reduced residue representatives, their checked
multiplication-by-a-remainder closure, a
set-valued left-coset construction with checked equal-or-disjoint carriers,
finite-support polynomial carrier with sum, convolution, degree,
division, gcd, and ideal interfaces, power congruences, the Legendre-symbol
specification, and concrete Gaussian-integer coordinate operations.

The current trust boundary is explicit in `todo.lit`. It is concentrated in
finite quotient/counting arguments, finite cyclic groups, generic polynomial
Euclidean theory, finite-field power maps, quadratic reciprocity, and Gaussian
Euclidean factorization. The project currently contains no `abstract_prop`.
Section VII additionally contains a direct, non-`trust` proof of the
exponent-kernel equality. Section VIII directly proves overlapping cosets
equal, a fixed-index finite unique-cover cardinality theorem, Lagrange's
divisibility theorem, and the closure of its reduced-residue multiplication
map. Euler's theorem still needs finite-product reindexing/cancellation (or a
finite-group power-at-cardinality and residue-power bridge). The session-prefix runner still has a separately recorded
no-diagnostic startup stall; ordinary release file gates remain available for
checkpoints.

A representative use is the checked Euclidean division interface:

```litex
by thm section2::euclidean_division_exists(a, d)
obtain q, r from exist q, r Z st {section2::euclidean_division_Z(a, d, q, r)}
```

`math_collections.md` explains the intended mathematical interfaces and their
dependency order. `todo.lit` is a comment-only ledger and is not exported.
