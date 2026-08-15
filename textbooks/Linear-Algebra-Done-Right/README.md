# Linear Algebra Done Right

> **Development status:** This module is developed in public and may contain
> work at different maturity levels. Its presence in the repository is not a
> completion claim; the verification evidence, explicit `trust` boundaries,
> and known limitations below describe what is currently established.

This publication snapshot contains the longest continuously verified prefix:
Sections 1A through 3D of Sheldon Axler's *Linear Algebra Done Right*, fourth
edition. The canonical workspace continues through 9D, but adding 3E to the
recursive project runner currently ends in a stack overflow; 3E and the later
files are therefore intentionally excluded here. Standalone exercises are
omitted.

## Run entrypoint and namespaces

Run the project with:

```sh
target/release/litex -compact -runner -r textbooks/Linear-Algebra-Done-Right
```

`litex.config` exports the chapter namespaces in source order:

```text
chap1a -> ... -> chap3d
```

Cross-section uses remain explicit, for example `chap2a::span`. An explicit
structure type on a binding selects that binding's default field view, so
`scalars &chap1a::ScalarSystem<s>` supports field notation such as
`scalars.add(a,b)`. Generic vector-space interfaces name the carrier
`VSet` and the corresponding `VectorSpace` structure `V`, keeping later
expressions concise as `V.add(u,v)` and `V.smul(a,u)`.

## Implemented mathematical surface

The implemented surface includes:

- the builtin complex carrier `C`, with callable conjugation, real and
  imaginary projections, and absolute value;
- the `ScalarSystem` and `VectorSpace` structures and their mathematical laws;
- finite coordinate lists, coordinate spaces, function spaces, subspaces,
  finite subspace sums, and direct sums;
- linear combinations, span, linear independence, bases, and dimension;
- linear maps and their pointwise operations, null spaces, ranges,
  rank-nullity statements, matrices, invertibility, products, quotients, and
  duality;
- complex conjugation and absolute value, polynomial evaluation, degree,
  division, zeros, and complex and real factorization statements;
- operators, eigenvalues and eigenvectors, minimal polynomials, invariant
  subspaces, triangularization, diagonalization, Gershgorin disks, and
  commuting-operator statements;
- inner products, norms, orthogonality, orthonormal bases, adjoints,
  Gram–Schmidt, spectral and singular-value decompositions, and operator
  geometry;
- generalized eigenvectors, nilpotent/Jordan structure, traces, bilinear and
  multilinear forms, alternating forms, determinants, characteristic
  polynomials, and the current tensor-product interfaces.

The finite tensor-family interface stores its indexed carriers, zeros,
additions, and scalar actions as exact bounded functions.  Thus a projected
field such as `family.carriers(k)` remains directly callable while retaining
the same finite `1..m` indexing used by the source.

A representative application shape is:

<!-- litex:skip-test -->
```litex
have x, y finite_seq(R, 2) = [1, 2], [3, 4]
\chap1a::coordinate_add<R, chap1a::real_scalars, 2>(x, y)
    $in finite_seq(R, 2)
```

## Verification and trust boundary

This is a runnable proof-debt-bearing translation, not a fully proved
formalization. Remaining `axiom` and direct `trust` boundaries are visible in
the exported section files. The
largest open boundaries concern selected algebraic structures, finite-list
recursion, basis and dimension infrastructure, matrix-coordinate
constructions, polynomial factorization, and the operator decomposition
theorems.

Chapter 1 has four localized boundaries: two complex-scalar adapter field
values after explicit `ScalarSystem` construction, the zero-length `FiniteList`
entry map in Section 1A, and packaging inherited subspace operations in
Section 1C. Dependent-list extensionality, the selected inverse equation,
binary direct-sum uniqueness, all five elementary
vector-space consequences in Section 1B, and both directions of the finite
and binary direct-sum criteria in Section 1C are checked.

Chapters 2 and 3 are fully source-represented and runnable. Chapter 2 has no
`axiom` and retains 35 localized direct `trust` steps (19, 5, and 11 in
Sections 2A, 2B, and 2C); clean release file gates pass for all three sections.
This includes checked proofs of exchange, basis reduction and extension,
complements, and the two-subspace dimension formula (Result 2.43), alongside
explicit remaining finite-list, basis-selection, and packaging debt. Chapter 3
remains a proof-debt-bearing development with 72 direct `trust` steps and 14
named source theorem or construction axioms.
Its boundaries cover matrix constructions, quotient well-definedness, and
duality. Column rank equals row rank, invertibility iff bijectivity, and the
equal-finite-dimension injective/surjective/invertible equivalences are now
checked rather than axiomatic; the corresponding equivalence of the two
one-sided inverse identities is checked as well.
Result 3.70 is also checked: equal-dimensional spaces over explicitly equal
scalar systems are isomorphic, and an isomorphism forces equal dimensions.
Result 3.71 is checked relative to the existing matrix selection boundaries:
the fixed-basis matrix map is a linear isomorphism onto the canonical
entrywise matrix vector space. Packaging that matrix structure accounts for
the additional localized direct `trust` step.
Definition 3.110 now identifies the callable dual carrier with the existing
linear-map carrier and checks the transport of its pointwise vector-space
structure, removing its direct selector trust. Result 3.111 is checked from
the general linear-map dimension theorem; its remaining local boundary is the
single reusable fact that the scalar field has dimension one.
Definition 3.112 now selects each coordinate functional from the checked
prescribed-basis-values interface, constructs the dual basis only from an
actual basis, and checks its Kronecker-delta values. Result 3.114 selects the
unique coordinate list and retains only the scalar delta-sum extraction
interface. Result 3.116 is a checked dimension-length consequence of one
localized direct trust asserting independence of the explicit dual list; the
former theorem-wide basis axiom has been removed.
Definition 3.118 now exposes the actual formula `dual_map(T)(phi)=phi∘T`
through ordinary composition-based functions instead of an opaque trusted
function declaration. Three localized projection/refinement trusts certify
the composed value, the outer linear map, and the source-facing pointwise
specification; Result 3.120 is a checked aggregate over three named localized
facets. Result 3.124 is likewise checked from its three closure facets.
Result 3.125 now constructs the restriction map `V' -> U'`, identifies its
kernel with the annihilator, records its surjectivity boundary, and derives
the annihilator dimension formula through rank-nullity and dual dimensions.
Result 3.127 is now a checked aggregate over four named extreme-annihilator
directions. Three directions are trust-free; the full-annihilator converse
retains one exact natural-number cancellation boundary after reusing Result
3.125's dimension formula.
Result 3.128 is now an ordinary aggregate over a named
`null(T')=annihilator(range(T))` boundary and a dimension-formula theorem whose
checked spine reuses Result 3.125 and rank-nullity. Its two remaining exact
boundaries are nested dual-map value projection and the final rank-nullity
arithmetic replay; dependent dimension transport is checked explicitly.
Result 3.129 is now fully checked with no new trust: surjectivity makes
`range(T)=W`, hence Result 3.127 and Result 3.128 make `null(T')={0}`; the
converse runs the same implications backward and unfolds full range into
surjectivity.
Result 3.130 is now an ordinary aggregate over a named
`range(T')=annihilator(null(T))` boundary and a checked dimension facet. The
dimension proof transports across the carrier equality, applies the
annihilator formula, and unfolds rank-nullity; only the functional
extension/nested-evaluation carrier equality remains localized trust.
Result 3.131 is now fully checked with no new trust: injectivity identifies
`null(T)` with zero, Results 3.127 and 3.130 identify `range(T')` with the full
dual space, and the new carrier-generic full-range bridge folds that equality
into surjectivity. The converse reverses the same chain.
Result 3.132 is now an ordinary entrywise matrix proof instead of a
theorem-wide axiom. It expands the two matrix columns, evaluates the selected
dual coordinates, and finishes by transpose extensionality. Two exact
pointwise facets remain localized: identifying the dual basis of `V'` with
evaluation on the original basis, and specializing `dual_map_spec` through a
nested dual-basis entry.
Result 3.40 now targets that canonical structure and derives its dimension
from an explicit matrix-unit-basis existence boundary. Result 3.72 is a
source-faithful theorem: finite-dimensional domain and codomain spaces over
equal scalar systems yield a nonempty finite-dimensional linear-map space of
dimension `dim(V) * dim(W)`. The remaining basis construction is exposed as a
named axiom rather than as extra premises on the public result.
Definition 3.73 now selects the unique coordinate list supplied by Result 2.28
and constructs its one-column matrix directly. Result 3.75 is checked: the
`k`th column of the matrix of a linear map is the coordinate matrix of the
image of the `k`th basis vector. Result 3.76 is checked as well: the coordinate
matrix of `T(v)` equals the matrix of `T` multiplied by the coordinate matrix
of `v`, with both bases explicit. Result 3.78 is no longer a theorem-wide
axiom: its column-space and `column_rank` chain is checked, with one localized
trust for transporting dimension from `range(T)` to the span of its coordinate
columns. Result 3.81 is checked by direct reuse of Result 3.43's explicit-basis
matrix-of-composition theorem. Result 3.82 is now a theorem as well: applying
that composition theorem in both basis orders proves the two coordinate-change
matrices are mutual inverses. Its supporting same-basis identity-matrix lemma
checks every entry from unit coordinate lists and retains one localized trust
only for the final bounded matrix-extensionality fold. Definition 3.80 now
selects `inverse_matrix` by genuine unique existence, so its inverse law is
available to callers; only the algebraic uniqueness step remains localized
trust. Result 3.84 is a theorem with no direct trust: two nested uses of Result
3.81 give the right-nested three-factor change-of-basis product, and Result
3.82 identifies its outer factor with the selected inverse matrix. Result 3.86
is also checked with no direct trust: the two inverse-map composition
identities yield both matrix inverse laws through Result 3.81, after which
inverse uniqueness identifies the selected inverse matrix.
In Section 3E, Result 3.92 is now a checked dimension theorem: it selects bases
at the two factor dimensions and derives the sum formula from the exact
`product_basis_exists` construction boundary, instead of trusting the public
dimension equality wholesale.
Definition 3.102 is checked as well: `quotient_add` and `quotient_smul` are
selected by unique existence after proving their translate values independent
of representatives. Result 3.103 is now checked too: representative equations
transport all seven law groups and package the exact quotient `VectorSpace`.
Definition 3.104's translate membership is checked. Result 3.105 is now a
checked source-facing subtraction theorem: a complement reduces the quotient
dimension to Result 3.94's direct-sum formula. Its sole new boundary is the
named `quotient_dimension_via_complement` axiom; the restricted quotient map's
linearity, injectivity, and surjectivity are checked separately, but the
verifier does not yet transport those anonymous-function facts onto one
`linear_map_space` binding. Definition 3.106 now selects `induced_map` by
checked unique existence, with representative independence derived from the
null-space condition. Result 3.107's factorization and subspace facts are
checked. Its sole remaining boundary is the named
`quotient_induced_map_higher_order_properties` axiom, which isolates
anonymous-function injectivity/range transport and restricted-codomain
isomorphism packaging.
Result 3.93 is now checked as well: direct-sum uniqueness makes the binary
addition map injective, and injectivity of that map recovers uniqueness of the
two summand coordinates. The general finite-family form remains represented by
iteration of this binary core.
The finite-dimensional rank-nullity theorem and both finite-dimensional
domain/codomain dimension obstructions are checked; linear-system consequences
remain explicit boundaries. The open
items are tracked as translated rather than zero-trust checkable interfaces.

Across all 36 exports, the current direct-`trust` count is 189 and the named
`axiom` count is 241, down from the captured 339-marker migration baseline.
The current release verifier checks
every export independently with `-f`; proof-debt cleanup happens directly in
this canonical workspace-owned module. No second publication snapshot is
maintained.

`math_collections.md` records the intended interfaces and their dependency
order. Working plans, item records, verifier notes, and blockers live in
`scripts/linear_algebra_done_right/`.
