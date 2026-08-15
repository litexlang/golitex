# Number Theory for Beginners

> **Development status:** This module is developed in public and may contain
> work at different maturity levels. Its presence in the repository is not a
> completion claim; the verification evidence, explicit `trust` boundaries,
> and known limitations below describe what is currently established.

This publication snapshot translates the non-exercise mathematical development
of André Weil and Maxwell Rosenlicht's *Number Theory for Beginners* through
Section XI. The canonical workspace contains later work, but Sections XII and
XIII are intentionally excluded from this verified publication prefix. Run it
from the repository root with:

```sh
target/release/litex -compact -runner -r textbooks/Number-Theory-For-Beginners
```

The publication project exports Sections I–XI and a checked finite-product support
module directly, with no citation package. Its
checked public surface includes
integer divisibility and Euclidean division, gcd and Bézout interfaces,
the proper-positive-divisor classification for a rational prime square,
the specialization that both factor norms in a nontrivial Gaussian split of
a rational prime equal that prime,
the canonical multiple set `mZ(m)` together with its membership
characterization, relative primality, finite-product prime divisibility and
prime-factorization existence,
congruences and residue classes, elementary group interfaces, the finite
integral-group-power uniqueness theorem,
residue-class carrier with its exact cardinality, the two-way membership
interface for reduced residue representatives, their checked
multiplication-by-a-remainder closure, a
set-valued left-coset construction with checked equal-or-disjoint carriers,
finite coset cardinality, constant-fibre cover counting, and Lagrange's
theorem together with its element-order divisibility corollary,
finite-product congruence and reindexing, and Euler's theorem by
permutation of reduced residues,
Fermat's little theorem for arbitrary integer representatives,
finite-support polynomial carrier with checked canonical zero,
coefficientwise addition, negation and subtraction, finite-convolution
multiplication, callable inverses for nonzero field coefficients,
singleton-supported scalar monomials, and a checked leading-term consumer
whose shifted product matches and cancels a chosen nonzero dividend
coefficient, together with nonzero-degree
objects, together with division, gcd, and ideal interfaces, power congruences, the Legendre-symbol
specification, Euler's quadratic-residue split, the mod-four criterion for
`-1` as a quadratic residue, and a native-complex Gaussian-integer carrier.
Section XIII uses builtin `C`, `i`, `re`, and `img` directly; its divisibility,
unit, associate, prime, ideal, factorization, and splitting interfaces no
longer expose coordinate-pair operations. Addition and multiplication closure
and the integer-valued norm selection are checked. The remaining Gaussian
proofs are translated with visible trust boundaries while the former
coordinate proofs are replayed against the native-complex kernel.

Theorem XIII.3 is now fully checked. In the composite case it specializes
both factor norms to the rational prime, rules out association of a factor
with its conjugate by the four Gaussian units, and uses Gaussian Euclid to
match every Gaussian prime divisor to one of the two conjugate factors.

The Gaussian factorization trace now has checked terminal constructors: units
produce an empty trace and Gaussian primes produce a singleton trace. Proper
divisor selection, strict descent of both factor norms, and concatenation of
two shorter traces are checked. The local norm-indexed proof has checked base
and composite-successor facts; its remaining trust is strong-induction
assembly. Positive norm plus nonunit status is checked to imply norm greater
than one. Gaussian divisibility is now explicitly reflexive and transitive,
both factors divide their product, every partial product in a factorization
trace divides its terminal value, and every listed prime factor therefore
divides the represented Gaussian integer.

The current module contains 10 executable `trust` statements, no
`abstract_prop`, and no `axiom` declarations. All 43 compatibility trusts
introduced by the builtin migration have been removed. Ten remaining
trusts are pre-existing mathematical proof debt in Sections IV, VII, IX--XI,
and XIII. Section
XIII's former compound native-complex multiplication and reconstruction
trusts are now checked by proving the two `re`/`img` equalities for typed
complex representatives and applying complex extensionality. In Section XI,
the exact identities `1 % p = 1` and `(p-1) % p = p-1` in the mod-four proof
now follow by instantiating Section II's checked Euclidean-division remainder
theorem.

Section XI's general prime power-congruence theorem no longer trusts its whole
equivalence. The forward direction is checked: a solution is first shown
coprime to the prime modulus, then Euler's theorem, `d|k`, and explicit
power-remainder normalization yield the reduced-power equation. Only the
converse remains trusted. Section X now exposes the selected-index and
order-divisibility interfaces, and the converse proof reaches the natural
exponent witness plus its local period-addition argument. The recorded
second-pass boundary is one remaining negative-shift carrier transport before
the final power-congruence witness can be folded.

Section XIII's rational-prime mod-four theorem now has a checked proof body.
It combines the Section XI minus-one quadratic-residue criterion with Gaussian
prime divisibility of `(x+i)(x-i)`, and uses the checked two-squares congruence
lemma for prime norms. The theorem and its XIII.3 splitting dependency are
now checked.

The Gaussian-prime classification corollary is also checked at its own
boundary. It chooses a rational prime divisor of the norm and applies Gaussian
prime-divides-product to the element and its conjugate. The cases `p=2`,
`p%4=3`, and `p%4=1` yield respectively the `1+i` associate class, the
rational-prime associate class, and rational-prime norm. Its former indirect
XIII.3 dependency is now checked as well.

Section XII now uses the same interface for eight bounded representative,
sum, negative-one, and doubled-index remainder identities. It also checks
zero-remainder transport, a product remainder's upper bound through an explicit
typed alias, signed-absolute-value normalization, positive-natural
discreteness through an explicit `N+` witness, and symbolic closed-range
cardinality through a checked universal interface. Section XII now has no
executable `trust`. Its Legendre-symbol layer also checks that quadratic
nonresidue status transports along congruence and that
`legendre_symbol_Z(p,a) = legendre_symbol_Z(p,b)` whenever `a` and `b` are
congruent modulo `p`. Thus the symbol is now exposed as a genuine function on
residue classes.
Gauss's lemma is now connected to that selected function by
`legendre_symbol_equals_gauss_sign_product`; its canonical specialization
identifies the symbol with the sign product on `1...h`, providing the numeric
endpoint that the remaining lattice-parity proof must consume. The next
geometric layer is now checked as well: `reciprocity_lattice_above` and
`reciprocity_lattice_below` partition `cart(1...h,1...k)` for distinct primes,
are disjoint and finite, and their cardinalities add to `h*k`. The subtler
parity bridge is now checked: the strict above-region cardinality and the
canonical negative-index cardinality are congruent modulo two. The two
cardinalities are not equal in general. Coordinate exchange identifies the
below region with the reversed above region, and
`theorem_XII_2_quadratic_reciprocity` combines both oriented parities with
the rectangle partition to prove the final Legendre-symbol sign formula.

The registered Section XII supplement now defines both the canonical row and
the named function-valued row family, proves that these rows uniquely cover
`reciprocity_lattice_above`, exposes finiteness of every fibre, and specializes
Section VIII's variable-fibre theorem to the checked total row-sum identity.
Each fixed row is now checked equal in cardinality to its bounded strict
multiple set, and a reusable arithmetic lemma normalizes that set to the
selected Euclidean quotient when the remainder is nonzero and the quotient is
within the supplied half-range. Distinct primality and the two half-range
equations now discharge those premises uniformly, and the entire strict
above-region cardinality is checked equal to Eisenstein's finite sum of
Euclidean quotients. A new registered parity supplement defines the
zero-or-one negative-sign indicator, identifies its finite sum with the
canonical negative-index cardinality, and checks both the exact per-index
signed Euclidean decomposition and its aggregate finite-sum identity. The
signed permuted half-range sum is the ordinary half-range sum plus an explicit
multiple of two. Combining it with the aggregate Euclidean equation proves
quotient-sum/negative-count parity; the existing Eisenstein row theorem then
yields the source-facing above-region/negative-count congruence. The final
supplement theorem now proves quadratic reciprocity without adding trust.

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
