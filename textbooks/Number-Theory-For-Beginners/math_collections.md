# Mathematical collections and interfaces

## 2026-08-01 verifier-boundary note

The current verifier checks the well-definedness of a finite product over
`1...h` before theorem premises are available.  Interfaces whose conclusions
contain that product therefore use `h N+` when nonemptiness follows
mathematically from a later premise such as `k N+` and `k <= h`.  In Section
XII this affects `sign_product_on_upper_range`,
`canonical_two_sign_product_at_cut`, and the four modulo-eight case helpers.
This is not a strengthening of the source theorem: every call site already
proves the positive lower bound.  It is the smallest stable typed interface at
the current well-definedness boundary.

Finite-product extensionality/reindexing, function-range containment,
closed-range cardinality, canonical remainder normalization, integer
discreteness, power normalization, and native-complex coordinate rules are now
checked through generic builtin rules or structural strategies. They are not
chapter-specific mathematical axioms.

The book develops elementary number theory from divisibility through quadratic
reciprocity and Gaussian integers. The interfaces below are the important
dependency nodes; chapter-local proof helpers should not be promoted merely to
make a proof shorter.

## Integer divisibility, Euclidean division, and gcd

`divides_Z(a,b)` means that `b = a*x` for an integer witness. Euclidean
division selects a quotient and bounded remainder, while `gcd_Z(a,b)` selects
the unique nonnegative common divisor divisible by every common divisor.
These are foundational because congruences, prime factorization, and linear
congruences all consume them.

`mZ(m)` is the canonical set of integer multiples of a natural number `m`.
It is a real set-valued `have fn`, and the public theorem
`mZ_membership_characterization` exposes its defining equality to later
modules. This matters because a later module cannot unfold the body of a
function declared in an earlier module; kernel and power arguments can instead
rewrite a membership in `mZ(m)` to `divides_Z(m, x)` explicitly. A wrapper
predicate for membership is rejected because the source construction is the
set itself, and ordinary set membership remains the consumer-facing form.

The intended forms are a real `prop` for divisibility, real `prop` relations
for quotient/remainder and gcd specifications, and `have fn ... by exist!` for
the selected quotient and gcd. Encoding either selected value only as a
predicate would lose the source-defined function used downstream. The
remaining restricted-gcd Bézout step should reuse the ordinary checked gcd
identity rather than introduce a second trusted theorem.

For a finite generator set `A \finite_subsets<Z>`, an integer linear
combination uses an ambient coefficient function `c fn(a Z) Z` and explicitly
restricts the weighted-term function to `A` when calling `finite_set_sum`.
This preserves the mathematical meaning that coefficients are assigned to
integers while satisfying the fold interface's exact-domain requirement. The
rejected form `c fn(a A) Z` loses the inherited fact that `a $in Z` inside the
anonymous function, so multiplication is not well-defined. The span and its
subtraction closure consume this interface. The all-zero weighted function is
now normalized by an explicit finite-sum equality chain.

## Primes and finite products

`is_prime_Z(p)` states the positive-divisor characterization of a prime.
Finite products are recursive integer-valued functions. Prime factorization
should expose a finite sequence of prime factors whose product is the input,
with uniqueness up to permutation.

The nearest rejected form is an opaque proposition saying merely that
factorization “exists”; the factor sequence and permutation relation matter to
later exponent and divisor arguments. The successor law and prime-divisor
induction over finite products are checked, as is factorization existence by
strong induction. Remaining holes concern permutation uniqueness and maximum
prime-power exponents. Corollary III.2.2 is checked using an auxiliary
induction property whose integer-carrier premise is explicit at every
finite-set step.

## Congruences and residue-class quotients

`congruent_mod(m,x,y)` is integer divisibility of `x-y` by `m`.
`residue_class_mod(m,x)` is the set of congruent representatives. The ideal
finite quotient carrier is the range of the class map on the standard
representatives `0,...,m-1`. Its Litex form is a set-valued `have fn` whose
defining range is finite. The current grammar does not admit `finite_set` as a
function codomain, so finiteness and cardinality are exposed as theorem-level
laws alongside class addition and multiplication.

The rejected form is an unrestricted set-builder over every subset of `Z`
with no finite presentation. The class and carrier remain real set-valued
functions, not an `abstract_prop`; the carrier's range formula supplies the
finite presentation. They feed
Euler's phi function, linear congruences, residue rings, finite fields, and
Euler's theorem. The open work is the induced operations and their laws, not
the elementary congruence algebra.

`coprime_remainders_mod(m)` is the finite set of standard representatives
prime to `m`. It remains a real set-valued `have fn`; its two checked
membership directions, `coprime_remainder_is_member_of_coprime_remainders_mod`
and `member_of_coprime_remainders_mod_is_coprime_remainder`, are the public
cross-file interface. This follows the earlier `mZ` pattern: a later chapter
must use the named membership theorem instead of depending on an earlier
file's function body unfolding. The Euler map is a source-facing theorem,
not a new global function: `multiplication_by_coprime_preserves_coprime_remainders`
proves that `(a*r) % m` remains in this carrier when `a` is coprime to `m`.

## Rings, zero divisors, and fields

A commutative ring is an additive abelian group with associative,
commutative, distributive multiplication; a unitary ring additionally selects
a multiplicative identity. These are distinct `prop` interfaces:
`is_commutative_ring(carrier,add,mul,zero)` and
`is_commutative_unitary_ring(carrier,add,mul,zero,one)`. Requiring a unit in
the basic ring predicate is rejected because the source introduces unitary
rings as a proper refinement. A zero divisor is a nonzero element that
annihilates another nonzero element, also represented by a `prop`.

Fields refine unitary rings by requiring every nonzero element to have a
unique multiplicative inverse. These nodes support the residue-class ring,
the prime-modulus field criterion, and polynomial theory over a field. The
ordinary integer and rational operations are representative use probes; they
need no wrapper objects around the builtin carriers.

## Finite groups, powers, orders, and cyclicity

Groups and subgroups are genuine structural predicates. A group-power relation
must describe finite multiplication for nonnegative exponents and inverse
powers for negative exponents. Element order is the least positive exponent
returning the identity; cyclicity says one element generates the carrier.
The finite cyclic classification must expose the actual power map from
integers (or residue classes) onto the group, with its homomorphism and
bijection laws. A residue-class map that does not mention the group,
operation, or generator is not a translation of that classification.

The intended lemma `nonnegative_group_power_is_unique` says that a finite
multiplication sequence is uniquely determined by its generator and exponent.
It is a theorem rather than a new selected power function: the useful result is
equality of any two existing sequence values, while the recursive normal form
remains local to the proof that needs it. A parameterized recursive template
would be the wrong current implementation boundary because its materialization
is presently blocked. A checked local recursive proof is retained in the
canonical module.

The theorem interface `group_power_add` makes the intended signed-power product
law explicit: values represented by exponents `a` and `b` multiply to a value
represented by `a + b`. Its local proof selects the inverse, normalizes all
finite sequences, and uses the group laws to commute inverse powers. That proof
is checked in the canonical module.

The theorem interface `zero_group_power_is_one` establishes the other basic
normal-form boundary: any signed-power witness at exponent zero has value
`one`. It is a source-facing theorem, not a global power construction. Its
private recursive normal form is used only to reduce the equal positive and
inverse exponents; the proof is checked in the canonical module.

`group_power_neg` constructs the inverse value at exponent `-a`
for every signed-power witness at exponent `a`. The source-facing theorem
`group_power_equality_iff_exponent_difference_in_kernel` is intended to prove
`x^a = x^b` exactly when `a-b` belongs to the exponent kernel: multiply by the
negative power for the forward implication, and add the `b`-power back for the
reverse implication. Its uniqueness helper remains inside that proof because
no other chapter consumes it. This supplies the kernel law needed by the
finite/infinite cyclic classification; constructing the actual index maps and
transporting cardinality remain open. The cyclic-classification dependency
chain still contains trust and is translated rather than checkable. Euler's
theorem no longer depends on that chain: its checked proof uses the
reduced-residue permutation directly.

The nearest rejected form is a circular `generated_subgroup`/power pair that
asserts the desired theorem by definition. These nodes support Lagrange,
Euler, primitive roots, discrete logarithm indices, and finite-field power
congruences. Lagrange's theorem must assume the ambient group laws in addition
to subgroup closure. Euler's theorem is a congruence statement
`congruent_mod(m, a^euler_phi(m), 1)`; raw remainder equality to `1` is not
valid for modulus `1`. Finite coset counting is currently blocked by
well-definedness for a function whose fibers are known finite only from the
active index set. The checked implementation uses a fixed-domain
constant-fibre cover instead. The nearby remaining hole is finite subgroup
cyclicity; Euler's theorem has been removed from this gap by a direct
reduced-residue product proof.

## Cosets and Lagrange counting

For a subgroup `H` of a group `G`, `left_coset(H, x)` is a genuine
set-valued function, represented by the member predicate
`left_coset_member(G, mul, H, x, y)`. The function form is necessary because
later arguments compare carriers, range over their members, and take their
finite cardinalities. The nearest rejected form is a bare predicate for
“being a coset”: it loses the carrier needed by the counting argument.

The three propositions
`cosets_overlap(G, C1, C2)`, `cosets_equal(G, C1, C2)`, and
`cosets_disjoint(G, C1, C2)` separate the logical roles in the source lemma.
The intended theorem
`left_cosets_overlap_implies_equal(G, mul, one, x, y, H)` consumes a common
element written as both `xh` and `yk`, then uses subgroup inverse closure to
transfer every `xu` to `yH` and conversely. Its downstream theorem
`left_cosets_equal_or_disjoint` is the exact qualitative partition interface.

The quantitative node is the fixed-domain interface
`fixed_unique_cover_of(U, D, S, T, F)`: the ambient index domain `D` remains
fixed while induction removes active elements of `T`. Its checked companion
`fixed_unique_cover_constant_size_holds(U,D,T,n)` records the constant-fibre
case directly, avoiding a dependent size function whose codomain the kernel
cannot establish at definition time. This fixed-domain form avoids changing
the type of `F` when an index is deleted; the nearest rejected form restricted
`F` to a changing subtype and made function equality unusable inside atomic
cover predicates. Instantiating the identity family on the range of
`x -> left_coset(H, x)` gives the checked Lagrange divisibility theorem.
The source-facing element-order corollary now reuses
`group_element_has_order`: its witness is a finite generated subgroup whose
cardinality is the element order, so Lagrange immediately yields divisibility
by `finite_set_size(G)`. The nearest rejected form duplicated “order” as a new
least-exponent predicate and lost the existing generated-subgroup witness.
Section VI
already supplies the finite reduced-residue group and its `euler_phi`
cardinality. Its multiplication-by-a-remainder map is now checked pointwise.
Section VIII packages the required map as a typed endomorphism of the finite
reduced-residue carrier, proves it bijective, reindexes the carrier product,
and cancels that product modulo `m`. The shared
`finite_product_toolkit` records the generic congruence, product-splitting,
bijective-reindexing, and cancellation interfaces used by this proof. This
direct route makes Euler's theorem checkable without waiting for the more
general finite-group power-at-cardinality bridge. Fermat's little theorem is
now a separate source-facing conclusion rather than an undocumented
specialization: the nondivisible case uses `phi(p)=p-1` and Euler, while the
divisible case factors `a^p-a` directly. The nearest rejected form assumed
relative primality and thereby weakened the book's all-integer statement.

## Power congruences over prime residue fields

`power_congruence_solvable_mod(p,k,a)` is the existence of an integer solution
to `x^k = a (mod p)`. In Theorem XI.1, `d = gcd(k,p-1)` and
`e*d = p-1` are shared hypotheses for the equivalence between solvability and
`a^e = 1 (mod p)`. The criterion is therefore a `prop` containing an
implication to an iff; it must not put the exponent equation on only one side
or quantify an otherwise unused `e`.

The nearest rejected form is a pair of wrapper predicates in which the
solution side ignores `e` while the reduced-power side requires
`e*d = p-1`. That shape states a false equivalence for arbitrary `e`.
The checked bridge from witness equations to congruence classes feeds Euler's
quadratic-residue criterion and the Legendre symbol. The general finite-field
power-map equivalence remains a single trusted interface. Its `k=2`
specialization now has a verifier-checked proof body: it proves
`gcd(2,p-1)=2`, invokes the general criterion once, and combines it with the
checked half-power `+1/-1` lemma. The source-facing corollary for `-1` is also
implemented through a genuine criterion prop; it uses natural-number parity
and states the stable result as `exist m N st {p=4*m+1}`. The nearest rejected
form was a theorem header containing a direct `forall ... <=>`, which the
current grammar does not accept. Both checked bodies remain downstream of the
single trusted general power-map interface rather than duplicating its debt.

## Polynomial Euclidean theory

The carrier is a finite-support coefficient function `fn(n N) K`. Polynomial
sum is coefficientwise, while multiplication is represented by a finite
convolution trace at each coefficient. Degree selects the last nonzero
coefficient, and a remainder is zero or has degree below the divisor. The
division, gcd, divisibility, ideal-closure, and principal-generator relations
are consequently typed over `polynomial_ring<K, zero>`.

Representing arbitrary polynomials as untyped `set` values or hiding their
operations in `abstract_prop polynomial_euclidean_data` is rejected. The
concrete carrier and operations are now implemented; the remaining holes are
the Euclidean-division, principal-ideal, and root-count proofs.

## Legendre symbols and quadratic reciprocity

The Legendre symbol is a selected integer in `{-1,0,1}` determined by the
divisible, quadratic-residue, and nonresidue cases. Its ideal Litex form is
`have fn legendre_symbol_Z ... by exist!` backed by a checked exhaustive and
exclusive case proof. Gauss's lemma relates it to the parity of a finite excess
set, and quadratic reciprocity follows from the lattice-count parity identity.

The nearest rejected form is trusting unique existence without proving the
three cases are exhaustive and disjoint. These interfaces depend on finite
residue representatives and the finite-field Euler criterion.

## Gaussian integers

A Gaussian integer is a native complex number whose real and imaginary parts
are integers. Its ideal Litex carrier is the named set-valued object

```litex
prop is_gaussian_integer(z C):
    exist x, y Z st {z = x + y * i}

have gaussian_integers power_set(C) =
    {z C: $is_gaussian_integer(z)}
```

Later declarations bind `z gaussian_integers` and use native complex addition,
multiplication, `i`, `re`, `img`, and complex extensionality directly.
The equivalent `re(z) $in Z` and `img(z) $in Z` characterization is a theorem,
not the carrier definition. The verifier now transports known complex
equalities through `re` and `img` and supplies coordinate formulas for native
complex sums, differences, and products. The existential `x+y*i` carrier
remains the source-facing construction and gives direct closure witnesses.
Conjugation is a formula-defined `have fn C -> C`. The integer norm is selected
with `have fn ... by exist!` from the unique integer equal to
`re(z)^2+img(z)^2`; this preserves the codomain required by descent even though
the current function-definition checker cannot consume the coordinate theorem
while checking a direct restricted-codomain equation.
Both are genuine function constructions;
divisibility, units, associates, and primality are `prop` relations on this
carrier. The norm is `re(z)^2 + img(z)^2`, not `C_abs(z)`: the former has the
integer codomain needed for descent, while `C_abs` is the ambient real modulus.

The nearest rejected forms are the former `cart(Z,Z)` representation with
chapter-local `gaussian_add` and `gaussian_mul` wrappers. Native `C` now
provides the mathematical object and operations directly, so retaining the
pair API or adding compatibility wrappers would create two incompatible
interfaces. Defining the carrier only by `re`/`img` membership remains
rejected: although it is extensionally natural and now usable in proofs, the
existential `x+y*i` definition matches the source and makes closure
constructive.

The typed dependency order is:

```text
C, i, re, img
  -> gaussian_integers                       [definition]
  -> gaussian_conjugate, gaussian_norm       [signature/definition]
  -> gaussian_divides, gaussian_unit,
     gaussian_associate, gaussian_prime      [signature/definition]
  -> Gaussian division and ideals            [proof]
  -> Euclid lemma and factorization traces   [proof/trust]
  -> rational-prime splitting and
     two-squares classification              [proof/trust]
```

There is no cycle: the carrier and its operations precede all relations, and
factorization consumes rather than defines primality. Euclidean division
constructs a Gaussian quotient by rounding rational coordinate formulas and
proves the remainder has smaller integer norm. The coordinate estimates use
`re` and `img`, while the quotient, remainder, ideals, products, and factor
sequences remain native complex objects.

The carrier, native addition and multiplication closure, coordinate
characterization, integer norm selection, norm multiplicativity, conjugation
algebra, unit-norm implication, and prime-norm lemma are checked. Proofs
formerly written against coordinate pairs are not treated as compatible
proofs: they must be replayed against the native carrier. Gaussian division,
principal-ideal descent, Bézout cancellation, and factorization induction
remain visible migration debt.

For Gaussian integers `a` and `b`,
`is_binary_gaussian_linear_combination(a,b,z)` is a real `prop`: it records
the existence of two Gaussian coefficients whose linear combination is `z`.
The collection of all such `z` is the set-valued
`have fn binary_gaussian_span(...) power_set(gaussian_integers)`. This separation is
important: membership is existential evidence, while the span itself must be
a reusable carrier that can satisfy `gaussian_ideal` and be passed to the
principal-generator theorem. Treating the span only as a predicate, or
selecting one coefficient tuple as a canonical function, is rejected because
neither shape represents the source's ideal of all combinations.

The span, ideal, prime-or-Bézout, and Euclid-lemma interfaces now use native
complex multiplication and addition. Their former pair-based proofs are
migration debt; the final Euclid case split is checked downstream of the
trusted principal-generation and cancellation steps.

`gaussian_prime_factorization_trace` now carries native-complex prime factors
and partial products. Existence and uniqueness retain their source-facing
interfaces but are trusted migration boundaries until the norm induction and
factor cancellation are replayed. Replacing the trace by a bare existential
remains rejected because it discards the data required for the permutation.

The source-facing Theorem XIII.2 now obtains its factorization from that
existence theorem. Its remaining uniqueness obligation is localized to
cancelling associate prime factors and constructing a permutation between two
factor sequences. It is therefore translated, not checkable.

The two alternative Gaussian-prime classifications use named existential
relations, such as `rational_prime_has_gaussian_split(p)`, before they enter a
disjunction. This is the appropriate `prop` form: it retains the existential
witnesses while giving the source-facing either-or statements atomic
disjuncts. A rejected form would place `exist ...` directly after `or`, which
the current fact grammar cannot parse.
