# Number Theory for Beginners

> **Development status:** This module is developed in public and may contain
> work at different maturity levels. Its presence in the repository is not a
> completion claim; the verification evidence, explicit `trust` boundaries,
> and known limitations below describe what is currently established.

This Litex project translates the non-exercise mathematical development of
André Weil and Maxwell Rosenlicht's *Number Theory for Beginners* in source
order. Run it from the repository root with:

```sh
RUST_MIN_STACK=8388608 target/release/litex -compact -runner -r scripts/number_theory_for_beginners/textbook
```

The project exports Sections I–XIII and a checked finite-product support
module directly, with no citation package. Its
checked public surface includes
integer divisibility and Euclidean division, gcd and Bézout interfaces,
the canonical multiple set `mZ(m)` together with its membership
characterization, relative primality, finite-product prime divisibility and
prime-factorization existence,
congruences and residue classes, elementary group interfaces, the finite
residue-class carrier with its exact cardinality, the two-way membership
interface for reduced residue representatives, their checked
multiplication-by-a-remainder closure, a
set-valued left-coset construction with checked equal-or-disjoint carriers,
finite coset cardinality, constant-fibre cover counting, and Lagrange's
theorem together with its element-order divisibility corollary,
finite-product congruence and reindexing, and Euler's theorem by
permutation of reduced residues,
Fermat's little theorem for arbitrary integer representatives,
finite-support polynomial carrier with sum, convolution, degree,
division, gcd, and ideal interfaces, power congruences, the Legendre-symbol
specification, Euler's quadratic-residue split, the mod-four criterion for
`-1` as a quadratic residue, and a native-complex Gaussian-integer carrier.
Section XIII uses builtin `C`, `i`, `re`, and `img` directly; its divisibility,
unit, associate, prime, ideal, factorization, and splitting interfaces no
longer expose coordinate-pair operations. Addition and multiplication closure
and the integer-valued norm selection are checked. The remaining Gaussian
proofs are translated with visible trust boundaries while the former
coordinate proofs are replayed against the native-complex kernel.

The current module contains 13 executable `trust` statements, no
`abstract_prop`, and no `axiom` declarations. All 43 compatibility trusts
introduced by the builtin migration have been removed. The remaining trusts
are pre-existing mathematical proof debt in Sections IV, VII, IX--XI, and
XIII; their exact interfaces remain recorded in the paired workspace
`scripts/number_theory_for_beginners/todo.md`.

All thirteen section files exist. This builtin migration does not claim a new
source-coverage audit; source-completeness work remains tracked separately.
The ordered project through Section XIII passes the release file gate:

```sh
target/release/litex -compact -runner -f scripts/number_theory_for_beginners/textbook/section13.lit
```

The complete canonical module also passes the release whole-book gate:

```sh
RUST_MIN_STACK=8388608 target/release/litex -compact -runner -r scripts/number_theory_for_beginners/textbook
```

Strict mode is used as a trust audit and, by design, stops at the first user
`trust` in Section IV. A strict zero-trust gate is therefore a later proof-debt
goal rather than the acceptance gate for this builtin migration.

A representative use is the checked Euclidean division interface:

```litex
by thm section2::euclidean_division_exists(a, d)
obtain q, r from exist q, r Z st {section2::euclidean_division_Z(a, d, q, r)}
```

`math_collections.md` explains the intended mathematical interfaces and their
dependency order. `todo.lit` is a comment-only ledger and is not exported.
