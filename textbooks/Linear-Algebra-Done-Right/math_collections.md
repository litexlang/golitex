# Mathematical Collections

## Purpose and scope

This manual records the mathematical spine for the draft translation of
Sheldon Axler's *Linear Algebra Done Right*, fourth edition. The
repository-local transcript dated 9 May 2026 is authoritative. The module keeps
Sections 1A through 9D in pedagogical order.

The exhaustive source-item coverage inventory belongs in the paired
`scripts/linear_algebra_done_right/` workspace. This file records only the
concepts and intermediate nodes that determine later interfaces.

## Modeling conventions

- A scalar domain is a carrier `s` together with a `ScalarSystem<s>` structure;
  it is not a predicate on untyped values. The two source instances are `R`
  and builtin `C`. The book's coordinate description of complex numbers is a
  source-facing theorem about `re`, `img`, and `i`, not a second complex
  carrier.
- A vector space is a carrier `VSet` together with a
  `V &VectorSpace<s,VSet>` structure. The structure owns its
  `scalars &ScalarSystem<s>` field, so later
  mathematics receives scalar and vector operations from one coherent bundle.
  Candidate operations and laws may still be tested by a relation before the
  structure is constructed. A theorem, `prop`, or template that already owns
  `space` reads scalar operations through `space.scalars`; it does not repeat
  a separate scalar-system parameter.
- Because this book works over `C` by default, its short public layer uses
  `V &CVectorSpace<VSet>`. Generic implementations remain available with
  `_general` names and consume `\as_vector_space<VSet,V>`. The reverse bridge
  is available only when a generic complex vector space's scalar system is the
  canonical `complex_scalars`.
- Collections use their narrowest existing carrier. Finite coordinate vectors
  use `finite_seq`; variable-length lists use `FiniteList`.
- A condition on supplied data is a `prop`. A set-valued construction such as
  span is a `have fn`. A canonical value such as dimension should be selected
  only after existence and uniqueness are available.
- `template` parameterizes declarations over carriers and structures; it is
  not itself a semantic layer. Source-facing results remain named even when a
  builtin or a more general checked interface supplies their proof.
- An explicit structure type on a binding selects its default field view.
  Thus `V &VectorSpace<s,VSet>` supports `V.zero`,
  `V.smul(a,v)`, and the nested access `V.scalars.mul(a,b)`. Source
  declarations use complete expressions rather than a pre-parser abbreviation
  layer; public theorem and definition parameters remain explicit only when
  the mathematical object is not already owned by a supplied structure.
- `axiom` and `trust` describe epistemic status, never mathematical kind. They
  remain visible below as dependency boundaries rather than changing the ideal
  interface.

## Mathematical spine

### Complex scalars and scalar systems

- **Ordinary meaning:** Litex's builtin `C` is the complex field. Every
  `z C` has the coordinate presentation `re(z) + img(z) * i`, while
  `ScalarSystem` packages the field operations needed by generic algebra.
- **Semantic role:** Builtin carrier plus bundled generic adapter.
- **Ideal Litex form:** builtin `C`, `i`, `re`, `img`, and `C_abs`; callable
  operation adapters; and a checked `complex_scalars &ScalarSystem<C>`.
- **Interface sketch:** `have complex_scalars &ScalarSystem<C>` with fields
  `0`, `1`, complex addition, negation, multiplication, and totalized inverse.
- **Nearest wrong alternative:** A local `struct Complex` duplicates builtin
  complex numbers and forces every later theorem through conversion or
  coordinate projection.
- **Dependencies:** Builtin complex arithmetic by `definition` and `law`;
  totalized inverse by `well_definedness`.
- **Downstream uses:** Generic polynomial and vector-space backends. Probe:
  `complex_scalars.add(z,w) = z + w`.
- **Allowable hole:** None for the carrier or scalar-system instance.

### Finite lists and coordinate spaces

- **Ordinary meaning:** A finite ordered list has a fixed length and callable
  entries; `F^n` is the positive-length coordinate carrier with pointwise
  operations.
- **Semantic role:** Structure, carrier family, and callable operations.
- **Ideal Litex form:** `FiniteList<s,n>` for lengths including zero;
  `finite_seq(s,n)` for source coordinate spaces; template-scoped `have fn`
  operations and a checked `VectorSpace` instance.
- **Interface sketch:**
  `\coordinate_add<s,scalars,n>(x,y) : finite_seq(s,n)`.
- **Nearest wrong alternative:** A set or predicate saying that entries exist
  loses order, length, and function application.
- **Dependencies:** Scalar system by `signature` and `definition`; function
  extensionality by `well_definedness`.
- **Downstream uses:** Linear combinations, independence, bases, and
  dimension.
- **Allowable hole:** Construction of the empty dependent entry map and general
  `FiniteList` extensionality are still explicit boundaries.

### Vector spaces

- **Ordinary meaning:** A carrier with vector zero, addition, complex scalar
  multiplication, and Axler's vector-space laws. A generic backend also
  supports an arbitrary `ScalarSystem<s>`.
- **Semantic role:** Two bundled structures connected by checked declaration
  families: book-facing `CVectorSpace<VSet>` and generic
  `VectorSpace<s,VSet>`.
- **Ideal Litex form:** `struct CVectorSpace<VSet>` owns `zero`, `add`, and
  `smul`, and stores one already-checked `general &VectorSpace<C,VSet>`;
  `struct VectorSpace<s,VSet>` additionally owns its scalar system.
  `template<VSet,V>: have as_vector_space &VectorSpace<C,VSet>` returns that
  stored generic view. A conditional reverse template supplies
  `as_c_vector_space`.
- **Interface sketch:** `V &CVectorSpace<VSet>` followed by `V.add(u,v)` and
  `V.smul(a,u)`; a generic theorem call receives
  `\as_vector_space<VSet,V>`.
- **Nearest wrong alternative:** A predicate such as `is_complex_vector_space`
  hides operations and makes ordinary field notation unavailable. Rebuilding a
  generic structure independently at every use also repeats membership
  inference and well-definedness work.
- **Dependencies:** Builtin `C` by `signature`; `complex_scalars` by bridge
  `definition`; vector-space laws by `law`.
- **Downstream uses:** Every complex-linear concept from subspaces onward.
  Probe: call one `_general` theorem with `\as_vector_space<VSet,V>` and recover
  a conclusion written with `V.add` and `V.smul`.
- **Allowable hole:** Existing selected coordinate, product, quotient, and
  function-space instances may retain their already-recorded proof debt. The
  C/generic bridges themselves must be checked.

### Inner-product spaces

- **Ordinary meaning:** A complex vector space with an inner product satisfying
  positivity, conjugate symmetry, and linearity.
- **Semantic role:** Book-facing bundled `CInnerProductSpace<VSet>` plus the
  existing generic `InnerProductSpace<s,VSet>` backend.
- **Ideal Litex form:** `CInnerProductSpace` owns a `CVectorSpace`, a
  `C`-valued inner product, and one already-checked
  `general &InnerProductSpace<C,VSet>`. A checked template returns that stored
  generic view, so generic results remain reusable without reconstructing the
  structure.
- **Interface sketch:** `Vinner &CInnerProductSpace<VSet>` and
  `Vinner.vector_space.add(u,v)`.
- **Nearest wrong alternative:** Requiring every source theorem to carry a
  scalar carrier, scalar geometry, scalar system, and generic vector-space
  bundle obscures the book's fixed complex setting.
- **Dependencies:** `CVectorSpace` by `signature`; complex conjugation and
  absolute value by `definition`; the generic bridge by `law`.
- **Downstream uses:** Orthogonality, adjoints, normal and self-adjoint
  operators, singular values, and spectral theorems.
- **Allowable hole:** Existing source theorems may retain their current named
  axioms or localized trust boundaries; the new structure and bridge add no
  proof debt.

### Product and quotient spaces

- **Ordinary meaning:** A binary product uses componentwise operations over one
  shared scalar system; a quotient carrier is the nonempty set of translates
  `v+U`, and the quotient map sends `v` to its translate.
- **Semantic role:** Carrier constructions plus callable operations and maps.
- **Ideal Litex form:** Product operations require
  `V.scalars = W.scalars`; `quotient_carrier` is an ordinary `nonempty_set`,
  and `quotient_map` is an ordinary `have fn`.
- **Interface sketch:** `\quotient_map<s,VSet,V>(U,v) =
  \translate<s,VSet,V>(U,v)`, with the translate proved to belong to
  `\quotient_carrier<s,VSet,V,U>`.
- **Nearest wrong alternative:** An unconditional product theorem would
  identify unrelated scalar actions. Trusted carrier promotion or a trusted
  quotient map would hide the checked `V.zero+U` witness and membership proof.
- **Dependencies:** Product laws depend on both factor structures and their
  shared scalar system. Quotient nonemptiness depends on `V.zero` and the
  translate definition.
- **Downstream uses:** Product dimension, quotient vector spaces, quotient
  dimension, and the first isomorphism theorem.
- **Allowable hole:** Folding the product tuple into `VectorSpace` and the
  representative-independent quotient operations remain localized proof debt.

### Subspaces, sums, and direct sums

- **Ordinary meaning:** A subspace is a subset closed under vector addition and
  scalar multiplication; a finite sum collects sums of one vector from each
  subspace; directness is uniqueness of that decomposition.
- **Semantic role:** Relations for subspace/directness; set-valued function for
  the sum.
- **Ideal Litex form:** `prop is_subspace`, `have fn subspace_sum`, and
  `prop is_direct_sum`.
- **Interface sketch:**
  `\subspace_sum<s,scalars,V,space,m>(parts) $subset V`.
- **Nearest wrong alternative:** A predicate about a proposed sum set would
  force every consumer to carry an extra candidate and equality.
- **Dependencies:** Vector-space laws by `definition`; finite summation by
  `definition` and `proof`; subspace-family hypotheses by `law`.
- **Downstream uses:** Span, independence, bases, and dimension.
- **Allowable hole:** A member-spec elimination bridge and the general finite
  direct-sum criterion remain; the latter must include the source's subspace
  hypotheses.

### Linear combinations, span, and independence

- **Ordinary meaning:** A coefficient list and a vector list determine a
  finite linear combination; span is the set of all such values;
  independence means that only zero coefficients give zero.
- **Semantic role:** Canonical finite-fold value, set-valued construction, and
  relation.
- **Ideal Litex form:** A locally constructive finite-fold `have fn` or a
  unique-existence selection for the value; `have fn span`; `prop
  is_linearly_independent`.
- **Interface sketch:** `\span<s,V,space,n>(vectors)` and, only for structural
  conclusions, `\span_carrier<s,V,space,n,vectors>` with a named equality to
  the concrete span.
- **Nearest wrong alternative:** A relation-only span or a trusted arbitrary
  value hides the object later chapters must use.
- **Dependencies:** Finite lists and vector-space operations by `definition`;
  finite recursion by `existence` and `uniqueness`.
- **Downstream uses:** Bases and dimension.
- **Allowable hole:** The Chapter 2 linear-combination, span, exchange, and
  deletion interfaces are present and runnable, but 35 localized direct trust
  boundaries remain across Chapter 2. Current verifier performance still
  benefits from the typed selected `span_carrier` plus its checked equality
  bridge when a structural predicate would otherwise expand the recursive
  selector; this is an implementation interface, not a trust boundary or a
  replacement for the concrete `span` construction.

### Formal polynomials

- **Ordinary meaning:** A polynomial is a finite formal coefficient sequence;
  evaluation at a scalar is a derived operation. Over finite fields, different
  formal polynomials may induce the same evaluation function.
- **Semantic role:** Bundled formal object with a normalized intrinsic degree.
- **Ideal Litex form:** `Polynomial<s,scalars>` owns `coefficients : N -> s`
  and `degree : PolynomialDegree`; its invariant identifies the zero sequence
  with degree minus infinity and otherwise records a nonzero leading
  coefficient with zero coefficients above it.
- **Interface sketch:** `p &Polynomial<s,scalars>`, `p.coefficients(k)`, and
  `p.degree`; `polynomial_space` is the structure carrier.
- **Nearest wrong alternative:** Defining `P(F)` as scalar-valued functions
  and postulating coefficient or degree uniqueness is false for finite fields.
- **Dependencies:** Scalar zero by `definition`; normalization by structure
  invariant; evaluation and arithmetic are derived finite folds.
- **Downstream uses:** Degree, polynomial vector spaces, roots,
  factorization, minimal and characteristic polynomials.
- **Allowable hole:** Evaluation and arithmetic migration in later chapters
  remains explicit follow-up work; degree existence and uniqueness itself has
  no trust boundary.

### Bases and dimension

- **Ordinary meaning:** A basis is an independent spanning list. Dimension is
  the common length of all bases of a finite-dimensional space.
- **Semantic role:** Relation followed by canonical selected value.
- **Ideal Litex form:** `prop is_basis`; prove basis existence and length
  uniqueness; then expose `have fn dimension ... by exist!`.
- **Interface sketch:** `\dimension<s,scalars,V,space>() : N`.
- **Nearest wrong alternative:** A primitive dimension axiom or a candidate
  relation alone does not expose a stable number with the required uniqueness
  dependency.
- **Dependencies:** Span and independence by `definition`; exchange/deletion by
  `proof`; basis existence and length uniqueness by `existence` and
  `uniqueness`; dimension by `selection`.
- **Downstream uses:** Dimension comparisons within the published slice.
- **Allowable hole:** Chapter 2 contains no `axiom` and retains 35 localized
  direct `trust` steps. Exchange, extraction, extension, inherited-carrier
  independence, dependent-length transport, basis-length uniqueness, and the
  two-subspace dimension formula are otherwise represented by checked
  interfaces; the remaining basis-selection and finite-list packaging debt is
  tracked in the paired workspace.

### Linear maps, null spaces, and ranges

- **Ordinary meaning:** A linear map is a typed callable function preserving
  addition and scalar multiplication. Its null space and range are canonical
  subsets of the domain and codomain.
- **Semantic role:** Relation on a supplied function, followed by set-valued
  constructions and a callable function-space carrier.
- **Ideal Litex form:** `prop is_linear_map`; template-scoped `have
  linear_map_space`; `have fn null_space`; and `have fn range_of`.
- **Interface sketch:**
  `T \chap3a::linear_map_space<s,VSet,WSet,V,W>` and
  `\chap3b::null_space<s,VSet,WSet,V,W>(T)`.
- **Nearest wrong alternative:** An opaque linear-map object would duplicate
  function application, while relation-only null/range interfaces would force
  every consumer to carry a candidate set.
- **Dependencies:** Vector-space operations by `signature` and `law`;
  preimage/image set builders by `definition`; basis extension and dimension
  by `proof`.
- **Downstream uses:** Rank-nullity, invertibility, matrices, quotients, and
  dual maps.
- **Allowable hole:** The basis-value extension theorem, linear-map
  function-space structure, and finite-dimensional rank-nullity package are
  checked. The lower-dimensional-codomain injectivity obstruction is also
  checked, as is the higher-dimensional-codomain surjectivity obstruction.
  The two generic linear-system consequences, matrix/rank constructions,
  quotient transport, and duality results remain explicit proof debt.

### Matrices and basis coordinates

- **Ordinary meaning:** A matrix is the builtin rectangular scalar array; the
  matrix of a linear map records the unique coordinates of each image of a
  domain basis vector in a codomain basis.
- **Semantic role:** Builtin carrier, callable matrix operations, and canonical
  basis-dependent selected matrices.
- **Ideal Litex form:** builtin `matrix(s,m,n)`; template-scoped `have fn`
  addition, scalar multiplication, multiplication, rows, columns, and
  transpose; `matrix_of_linear_map` selected from its coordinate relation.
- **Interface sketch:**
  `\matrix_of_linear_map<s,VSet,WSet,V,W,n,m>(domain_basis,codomain_basis,T)`.
- **Nearest wrong alternative:** A parallel list-of-lists carrier discards
  builtin shape checking; omitting the two bases makes the matrix
  mathematically ambiguous.
- **Dependencies:** Basis coordinates by `existence` and `uniqueness`; finite
  scalar sums by `definition`; matrix extensionality by `well_definedness`.
- **Downstream uses:** Matrix products, rank, change of basis, operator
  matrices, determinants, and spectral theory.
- **Allowable hole:** Coordinate selection, rank selection, factorization, and
  row-rank/column-rank equality retain visible debt.

### Inverses, quotients, and duals

- **Ordinary meaning:** Inverses are uniquely selected two-sided inverses;
  quotient vectors are translates modulo a subspace; dual vectors are linear
  scalar-valued functions.
- **Semantic role:** Candidate relations followed by selected functions,
  carrier/set-valued constructions, and inherited vector-space structures.
- **Ideal Litex form:** `prop is_inverse_linear_map` plus
  `have fn inverse_linear_map ... by exist!`; callable `translate`,
  `quotient_carrier`, and `quotient_map`; callable `dual_space`, `dual_map`,
  and `annihilator`.
- **Interface sketch:** `\inverse_linear_map<...>(T)(w)`,
  `\quotient_map<...>(U,v)`, and
  `\dual_map<...>(T)(phi)(v)`.
- **Nearest wrong alternative:** A bare invertibility proposition does not
  provide the inverse required downstream; an abstract quotient/dual
  predicate does not provide elements or callable maps.
- **Dependencies:** Unique preimages by `existence/uniqueness`; translate
  equality and representative independence by `well_definedness`; linear-map
  composition and basis coordinates by `definition/proof`.
- **Downstream uses:** Isomorphism theorems, quotient dimension, first
  isomorphism, annihilators, duality, transpose, and rank.
- **Allowable hole:** Quotient representative independence, dependent-carrier
  structure transport, dual-basis construction, and the major duality
  dimension theorems remain visible proof debt.

## Chapters 2–3 interface and naming audit

| Declaration kind | Mathematical meaning | Existing candidates | Selected name | Rejected alternative |
| --- | --- | --- | --- | --- |
| set-valued function | span of a finite vector list | span, linear span | `span` | `is_span` would hide the set used by membership and subspace arguments |
| relation | a list is linearly independent | independent, is linearly independent | `is_linearly_independent` | `linear_independence` would read like an object rather than a judgment |
| canonical selection | common basis length | dimension, dim | `dimension` | a primitive number or relation-only encoding would hide existence and uniqueness |
| relation | supplied function is linear | linear map, is linear map | `is_linear_map` | bundling an opaque map would duplicate ordinary function application |
| set-valued function | kernel/null space of a map | kernel, null space | `null_space` | the source consistently uses “null space”; an alias would publish two names |
| set-valued function | image/range of a map | image, range | `range_of` | plain `range` risks collision with numeric ranges and hides the source object in call sites |
| canonical selection | basis-dependent matrix of a map | matrix of linear map | `matrix_of_linear_map` | `matrix_of` omits the mathematical object and two-basis dependency |
| relation/selection | two-sided inverse and selected inverse | inverse linear map | `is_inverse_linear_map` / `inverse_linear_map` | one overloaded predicate/function name would conflate candidate and selected inverse |
| set-valued function | annihilator of a subspace | annihilator | `annihilator` | a relation on a proposed set would obstruct later dimension and equality statements |

## Chapter 1 interface and naming audit

| Declaration kind | Mathematical meaning | Existing candidates | Selected name | Rejected alternative |
| --- | --- | --- | --- | --- |
| structure | field operations needed by generic algebra | field, scalar field, scalar system | `ScalarSystem` | `Field` would overstate the current book-local interface and collide with broader algebra terminology |
| structure | a carrier with callable vector operations and laws | vector space | `VectorSpace` | `is_vector_space` alone hides the operations later chapters apply |
| structure | Axler's default complex vector-space view | complex vector space | `CVectorSpace` | repeating the generic scalar carrier in every source-facing theorem obscures the book's default setting |
| relation | a candidate subset is closed under vector operations | subspace, is subspace | `is_subspace` | `subspace` would read like the subset-valued object rather than the judgment |
| set-valued function | all finite sums from supplied subspaces | sum of subspaces, subspace sum | `subspace_sum` | a relation on a proposed result set would make every caller carry an extra equality |
| relation | decompositions in a supplied sum are unique | direct sum, is direct sum | `is_direct_sum` | a selected object is unnecessary because the summand family is already supplied |

## Dependency map

Edge labels used below are `signature`, `definition`, `law`, `proof`,
`selection`, and `trust`.

~~~text
Builtin C and R
  -[signature/definition]-> ScalarSystem
ScalarSystem
  -[signature/law]-> finite coordinate operations
  -[signature/law]-> VectorSpace
VectorSpace<C,VSet> + canonical complex_scalars
  -[law]-> CVectorSpace<VSet>
VectorSpace + candidate subset U
  -[definition]-> is_subspace
is_subspace + restricted operations
  -[trust]-> subspace_vector_space
VectorSpace + finite subspace family
  -[definition]-> subspace_sum
  -[definition]-> is_direct_sum
subspace laws + finite-sum lemmas
  -[proof]-> direct-sum zero criterion
binary subspace sum + intersection
  -[proof]-> binary direct-sum criterion
VectorSpace + unique additive inverse
  -[selection]-> vector_neg

subspace_sum
  -[definition]-> span
span + linear independence
  -[proof]-> basis
basis existence + basis-length uniqueness
  -[selection]-> dimension
VectorSpace + typed functions
  -[definition/law]-> linear_map_space
linear_map_space
  -[definition]-> null_space and range_of
null_space + range_of + dimension
  -[proof]-> rank-nullity
bases + unique coordinates + linear maps
  -[selection]-> matrix_of_linear_map
matrix_of_linear_map + finite scalar sums
  -[definition/proof]-> matrix multiplication and rank
invertibility + inverse uniqueness
  -[selection]-> inverse_linear_map
subspace translates + representative independence
  -[definition/law]-> quotient space and quotient map
linear_map_space into scalars
  -[definition]-> dual_space
dual basis + composition
  -[selection/proof]-> dual_map and annihilator
~~~

This order is refined by the source-ordered exports from `chap1a` through
`chap9d`. Short names in the C-facing layer depend on their `_general`
backends; bridge templates are the only edges between those two layers.
