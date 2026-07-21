# Mathematical Collections

## Purpose and scope

This manual records the mathematical spine for the implemented Chapters 1–4
and Chapter 5 operator layer
of Sheldon Axler's *Linear Algebra Done Right*, fourth edition. The
repository-local transcript dated 9 May 2026 is authoritative. The module keeps
the source's definitions and named results in pedagogical order, omits
standalone exercises, and serves both as a readable formalization and as a
pressure test for Litex structures, finite constructions, canonical choices,
and proof automation.

The exhaustive source-item coverage inventory belongs in the paired
`scripts/linear_algebra_done_right/` workspace. This file records only the
concepts and intermediate nodes that determine later interfaces.

## Modeling conventions

- A scalar domain is a carrier `s` together with a `ScalarSystem<s>` structure;
  it is not a predicate on untyped values. The two source instances are `R`
  and the concrete pair carrier `Complex`.
- A vector space is a carrier `V` together with a `VectorSpace<s,scalars,V>`
  structure. Candidate operations and laws may be tested by a relation, but
  later mathematics receives callable operations through the structure.
- Collections use their narrowest existing carrier. Finite coordinate vectors
  use `finite_seq`; variable-length lists use `FiniteList`; matrices use the
  builtin `matrix` carrier.
- A condition on supplied data is a `prop`. A set-valued construction such as
  span, null space, range, or annihilator is a `have fn`. A canonical value
  such as dimension or inverse should be selected only after existence and
  uniqueness are available.
- `template` parameterizes declarations over carriers and structures; it is
  not itself a semantic layer. Source-facing results remain named even when a
  builtin or a more general checked interface supplies their proof.
- File-local macros abbreviate repeated fully qualified types, structure
  views, and function families. In particular, `@ScalarSystem` is the bare
  type `ScalarSystem<s>`, whereas `@Scalars` is the view of the supplied
  `scalars` instance. These macros do not create concepts or dependencies,
  and public theorem and definition parameters remain explicit.
- `axiom` and `trust` describe epistemic status, never mathematical kind. They
  remain visible below as dependency boundaries rather than changing the ideal
  interface.

## Mathematical spine

### Complex scalars and scalar systems

- **Ordinary meaning:** `Complex` is `R x R` with coordinate arithmetic;
  `ScalarSystem` packages the zero, one, addition, negation, multiplication,
  inverse, and field laws used uniformly later.
- **Semantic role:** Carrier plus bundled structure.
- **Ideal Litex form:** `struct Complex`; callable `have fn` operations; and
  `struct ScalarSystem<s>` with checked real and complex instances.
- **Interface sketch:** `have complex_scalars &ScalarSystem<&Complex>`.
- **Nearest wrong alternative:** A predicate `is_complex(z)` or a bare global
  carrier `F` would not expose values and operations to later maps.
- **Dependencies:** `R` by `signature`; coordinate formulas by `definition`;
  inverse by `well_definedness` and `uniqueness`.
- **Downstream uses:** Every vector-space, polynomial, matrix, quotient, and
  dual-space declaration. Probe: apply `ScalarSystem.add(a,b)` and obtain a
  value in `s`.
- **Allowable hole:** None in the ideal interface. The real instance is now
  checked from explicit `real_add`, `real_neg`, `real_mul`, and `real_inv`
  laws. Complex normalization, inverse, and selected-instance debt remain.

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
- **Downstream uses:** Linear combinations, bases, matrices, coefficient lists,
  and finite factorization data.
- **Allowable hole:** Construction of the empty dependent entry map and general
  `FiniteList` extensionality are still explicit boundaries.

### Vector spaces

- **Ordinary meaning:** A carrier with vector zero, addition, scalar
  multiplication, and Axler's vector-space laws.
- **Semantic role:** Bundled structure; `is_vector_space` is the candidate-law
  relation corresponding to structure membership.
- **Ideal Litex form:** `struct VectorSpace<s,scalars,V>`.
- **Interface sketch:** `space &VectorSpace<s,scalars,V>` followed by
  `&VectorSpace{space}.add(u,v)`.
- **Nearest wrong alternative:** A proposition that hides the three operations
  cannot support ordinary vector expressions or structures inherited by a
  subspace, product, quotient, or function space.
- **Dependencies:** Scalar system by `signature` and `law`; carrier and
  operations by `signature`.
- **Downstream uses:** Every concept from subspaces onward. Probe: apply vector
  addition and scalar multiplication, then cite the structure laws.
- **Allowable hole:** The structure form is fixed, and laws now project
  directly after each quantified law group was narrowed to the variables it
  actually uses. Several selected concrete/inherited instances remain debt.

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
- **Downstream uses:** Span, complements, quotient spaces, dimension formulas,
  and the first isomorphism theorem.
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
- **Interface sketch:** `\span<s,scalars,V,space,n>(vectors)`.
- **Nearest wrong alternative:** A relation-only span or a trusted arbitrary
  value hides the object later chapters must use.
- **Dependencies:** Finite lists and vector-space operations by `definition`;
  finite recursion by `existence` and `uniqueness`.
- **Downstream uses:** Bases, dimension, ranges, row/column rank, polynomial
  coefficient representations.
- **Allowable hole:** The linear-combination selector now has a checked
  unique-existence spine, but some entry laws and all exchange/deletion results
  remain explicit debt.

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
- **Downstream uses:** The fundamental theorem of linear maps, rank,
  isomorphism, quotient/product/dual dimensions.
- **Allowable hole:** The current interface shape is correct, but the
  exchange, extraction, extension, and basis-length theorems remain named
  axioms.

### Function-based polynomials

- **Ordinary meaning:** A polynomial is a scalar-valued function represented
  by finitely many coefficients; degree is the unique largest nonzero
  coefficient index, with a separate value for the zero polynomial.
- **Semantic role:** Function-space subset, finite representation relation,
  and canonical selected degree.
- **Ideal Litex form:** Set-valued `polynomial_space`, coefficient/representation
  relations, and `have fn degree ... by exist!` after uniqueness.
- **Interface sketch:** `p \polynomial_space<s,scalars>` and `p(lambda)`.
- **Nearest wrong alternative:** Treating a polynomial as an unrestricted
  function loses finite degree and coefficient uniqueness; treating it only as
  coefficient data loses evaluation.
- **Dependencies:** Scalar system and finite lists by `definition`; finite
  coefficient uniqueness by `proof` and `uniqueness`.
- **Downstream uses:** Chapter 4 zeros, division, factorization, conjugate-root
  arguments, and later operator polynomials.
- **Allowable hole:** Degree existence/uniqueness and polynomial division are
  still named proof boundaries.

### Linear maps and their vector space

- **Ordinary meaning:** A linear map preserves addition and scalar
  multiplication; linear maps form a vector space under pointwise operations,
  and compose associatively.
- **Semantic role:** Relation on typed functions, set-valued function space,
  callable operations, and bundled selected structure.
- **Ideal Litex form:** `prop is_linear_map`, `have fn linear_map_space`,
  pointwise `have fn` operations, and a checked `VectorSpace` instance.
- **Interface sketch:**
  `T \linear_map_space<s,scalars,V,W,Vspace,Wspace>` and `T(v)`.
- **Nearest wrong alternative:** A predicate about an untyped map or an opaque
  linear-map object would obstruct ordinary application and composition.
- **Dependencies:** Domain and codomain vector spaces by `signature` and `law`;
  function extensionality by `well_definedness`.
- **Downstream uses:** Null space, range, matrices, inverses, quotient-induced
  maps, and dual maps.
- **Allowable hole:** Pointwise operation closure, the selected vector-space
  instance, and composition closure remain trusted/axiomatic.

### Null space, range, and the fundamental dimension theorem

- **Ordinary meaning:** Null space is the preimage of zero; range is the image;
  a finite-dimensional domain decomposes dimension into nullity plus range
  dimension.
- **Semantic role:** Set-valued constructions and mathematical results.
- **Ideal Litex form:** `have fn null_space`, `have fn range`, checked subspace
  theorems, then the named fundamental theorem.
- **Interface sketch:** `\null_space(...)(T)` and `\range(...)(T)`.
- **Nearest wrong alternative:** Relations with proposed output sets make later
  dimension and quotient statements carry avoidable witnesses.
- **Dependencies:** Linear maps by `definition`; subspace closure by `proof`;
  bases/dimension by `proof`.
- **Downstream uses:** Injectivity/surjectivity criteria, systems of equations,
  rank, quotient-induced maps, and annihilators.
- **Allowable hole:** The set-valued forms are implemented, but their subspace
  facts and the fundamental theorem remain named axioms.

### Matrices, matrices of maps, and rank

- **Ordinary meaning:** A matrix is the builtin rectangular scalar array;
  chosen bases identify a linear map with a matrix; column and row rank are
  dimensions of the corresponding spans.
- **Semantic role:** Builtin carrier, canonical construction from bases, and
  canonical natural-valued functions.
- **Ideal Litex form:** Reuse `matrix(s,m,n)`; construct `matrix_of_linear_map`;
  define rank through `span` and `dimension`.
- **Interface sketch:** `\matrix_of_linear_map(...)(basisV,basisW,T)`.
- **Nearest wrong alternative:** A parallel list-of-lists matrix theory or an
  arbitrary bounded rank selector loses the source definition and builtin
  matrix operations.
- **Dependencies:** Bases and coordinates by `definition` and `uniqueness`;
  linear maps by `signature`; span/dimension by `definition`; matrix
  multiplication by `well_definedness`.
- **Downstream uses:** Products of maps, change of basis, inverse matrices,
  rank theorems, and dual-transpose results.
- **Allowable hole:** Matrix selection, multiplication closure, and both rank
  definitions remain direct trust; most matrix identities remain axioms.

### Inverses and isomorphisms

- **Ordinary meaning:** An inverse is the unique two-sided inverse linear map;
  an isomorphism is an invertible linear map.
- **Semantic role:** Candidate relation, uniqueness result, and canonical
  selected function.
- **Ideal Litex form:** `prop is_invertible_linear_map`, prove inverse
  uniqueness and existence under the predicate, then `have fn ... by exist!`.
- **Interface sketch:** `\inverse_linear_map(...)(T)(w)`.
- **Nearest wrong alternative:** A trusted arbitrary inverse function severs
  the required existence/uniqueness proof and obscures its linearity.
- **Dependencies:** Linear-map composition and identity by `definition`;
  inverse existence and uniqueness by `existence` and `uniqueness`.
- **Downstream uses:** Isomorphism classification, change of basis, inverse
  matrices, quotient-induced isomorphisms.
- **Allowable hole:** The present inverse selector and most equivalence results
  are explicit debt.

### Products and quotient spaces

- **Ordinary meaning:** A product carries componentwise operations. A quotient
  consists of translates `v+U`, with operations independent of chosen
  representatives.
- **Semantic role:** Carrier constructions, callable operations, selected
  structures, and well-defined maps.
- **Ideal Litex form:** Set-valued product/quotient carriers, explicit
  componentwise or representative operations, proofs of well-definedness, then
  checked `VectorSpace` instances.
- **Interface sketch:** `\quotient_space(...)(U)` and `\quotient_map(...)(U,v)`.
- **Nearest wrong alternative:** An opaque `abstract_prop quotient_space`
  cannot provide quotient elements, operations, or the induced map.
- **Dependencies:** Vector spaces and subspaces by `signature`; translates by
  `definition`; representative independence by `well_definedness`; quotient
  structure by `law`.
- **Downstream uses:** Dimension of quotients and the first isomorphism theorem.
- **Allowable hole:** Product and quotient selected structures, quotient
  nonemptiness, representative-independent operations, and induced-map laws
  remain explicit debt.

### Dual spaces, annihilators, and dual maps

- **Ordinary meaning:** The dual is the linear-map space into the scalar field;
  the annihilator consists of functionals vanishing on a subset; a dual map
  acts by precomposition.
- **Semantic role:** Function-space construction, selected vector space,
  set-valued construction, and callable map.
- **Ideal Litex form:** Reuse `linear_map_space` for the dual carrier; construct
  its vector-space instance; use `have fn annihilator` and `have fn dual_map`.
- **Interface sketch:** `\dual_map(...)(T)(phi)`.
- **Nearest wrong alternative:** Relations `has_dual` or `is_annihilator`
  would hide objects that later code must apply.
- **Dependencies:** Linear-map space by `definition`; scalar vector space and
  pointwise structure by `law`; composition by `definition`; bases/dimension
  by `proof`.
- **Downstream uses:** Dual bases, annihilator dimensions, injective/surjective
  duality, transpose, and the second proof of row rank equals column rank.
- **Allowable hole:** Scalar/dual selected structures, dual bases/maps, and
  dimension/annihilator theorems remain explicit debt.

### Zeros and factorization of polynomials

- **Ordinary meaning:** A zero is an input where a polynomial evaluates to
  zero; division by a linear factor removes a zero; complex polynomials split
  into linear factors, while real polynomials split into linear and irreducible
  quadratic factors.
- **Semantic role:** Relation, algebraic results, and one external analytic
  theorem boundary.
- **Ideal Litex form:** `prop is_zero_of_polynomial`; checked division and
  induction theorems; a clearly isolated analytic input for the first version
  of the fundamental theorem of algebra.
- **Interface sketch:** `$is_zero_of_polynomial(s,scalars,p,lambda)`.
- **Nearest wrong alternative:** Folding factorization conclusions into a
  polynomial admissibility predicate would make the theorems tautological.
- **Dependencies:** Polynomial representation by `definition`; finite
  induction and division by `proof`; complex analysis by `trust/source` only
  for the analytic FTA input.
- **Downstream uses:** Complex and real factorization, conjugate roots, and
  later eigenvalue theory.
- **Allowable hole:** The analytic minimum-modulus input may remain a visible
  external boundary; algebraic division and factorization consequences should
  be proved from it.

### Operators and invariant subspaces

- **Ordinary meaning:** An operator is a linear map from a vector space to
  itself. A subspace is invariant under an operator when applying the operator
  never leaves that subspace.
- **Semantic role:** Existing linear-map carrier specialized to equal domain
  and codomain, plus a relation on an operator and a supplied subset.
- **Ideal Litex form:** Reuse `linear_map_space` for the operator carrier and
  define `prop is_invariant_subspace` with the subspace condition and one
  closure clause.
- **Interface sketch:**
  `$is_invariant_subspace(s,scalars,V,Vspace,T,U)`.
- **Nearest wrong alternative:** A new opaque operator structure duplicates
  callable linear maps; a set-valued invariant-subspace selector would falsely
  choose one subspace when many exist.
- **Dependencies:** Linear maps by `signature`; subspaces and map application
  by `definition`.
- **Downstream uses:** Restrictions, eigenspaces, triangularization,
  diagonalization, commuting operators, and decomposition arguments.
- **Allowable hole:** None in the relation itself. Existence of useful proper
  invariant subspaces may depend on later eigenvalue results.

### Eigenvalues and eigenvectors

- **Ordinary meaning:** A scalar is an eigenvalue of `T` when a nonzero vector
  is scaled by `T`; such a vector is an eigenvector for that scalar.
- **Semantic role:** Relations on existing scalar, vector, and operator data.
- **Ideal Litex form:** `prop is_eigenvalue` with an existential vector and
  `prop is_eigenvector` with the nonzero and eigen-equation clauses.
- **Interface sketch:**
  `$is_eigenvector(s,scalars,V,Vspace,T,lambda,v)`.
- **Nearest wrong alternative:** Selecting a canonical eigenvalue or
  eigenvector is mathematically unjustified because neither need exist or be
  unique.
- **Dependencies:** Operator application and scalar multiplication by
  `definition`; null spaces and finite-dimensional invertibility equivalences
  by `proof`.
- **Downstream uses:** Eigenspaces, the minimal polynomial, triangular and
  diagonal forms, spectral results, and simultaneous eigenvector arguments.
- **Allowable hole:** Independence of eigenvectors and the bound on distinct
  eigenvalues may temporarily reuse the explicit finite-list exchange debt
  from Chapter 2.

### Operator powers

- **Ordinary meaning:** `T^0` is the identity operator, positive powers are
  repeated composition, and negative powers are powers of the inverse when
  `T` is invertible.
- **Semantic role:** Callable recursively defined construction, with a
  restricted callable construction for negative exponents.
- **Ideal Litex form:** `have fn operator_power(T,n)` by induction on `n`, and
  `have fn negative_operator_power(T,n)` only on invertible operators.
- **Interface sketch:** `\operator_power(...)(T,n) : operator_space`.
- **Nearest wrong alternative:** A proposition saying that an output is a
  power leaves later polynomial evaluation unable to apply or compose it.
- **Dependencies:** Identity and composition by `definition`; inverse by
  `signature`, `existence`, and `uniqueness` for negative powers.
- **Downstream uses:** Polynomial evaluation at an operator, minimal
  polynomials, generalized eigenvectors, nilpotent operators, and exponent
  laws.
- **Allowable hole:** General exponent laws may remain named proof debt while
  the recursive values themselves stay callable.

### Polynomials applied to operators

- **Ordinary meaning:** A finite coefficient representation
  `p(z)=a_0+...+a_m z^m` determines the operator
  `p(T)=a_0 I+...+a_m T^m`.
- **Semantic role:** Candidate-value relation followed by canonical selection;
  polynomial product remains an ordinary callable function.
- **Ideal Litex form:** Define a relation tying a polynomial representation to
  the corresponding finite linear combination of operator powers, prove the
  resulting operator independent of the representation, then expose
  `have fn polynomial_at_operator ... by exist!`.
- **Interface sketch:** `\polynomial_at_operator(...)(p,T) : operator_space`.
- **Nearest wrong alternative:** An uninterpreted trusted operator-valued
  function has no usable evaluation law; a proposition-only candidate forces
  every later theorem to carry an avoidable output witness.
- **Dependencies:** Polynomial representation, operator powers, the vector
  space of linear maps, and finite linear combinations by `definition`;
  coefficient uniqueness by `well_definedness` and `uniqueness`.
- **Downstream uses:** Multiplicativity, invariant null/range spaces, minimal
  polynomials, polynomial factor arguments, and primary decomposition.
- **Allowable hole:** Until coefficient-representation uniqueness is connected
  to operator linear combinations, the selector and its specification may be
  an explicit `trust` boundary. Multiplicativity remains a named theorem, not
  part of the definition.

### Minimal polynomial

- **Ordinary meaning:** A monic polynomial has leading coefficient one. For a
  finite-dimensional operator, the minimal polynomial is the unique monic
  polynomial of least degree that evaluates to the zero operator.
- **Semantic role:** Monicity and annihilation are relations; minimality is a
  candidate relation; the minimal polynomial is a canonical selected
  polynomial only after existence and uniqueness.
- **Ideal Litex form:** `prop is_monic_polynomial_of_degree`, `prop
  annihilates_operator`, `prop is_minimal_polynomial_of`, a source theorem
  proving unique existence and the degree bound, then `have fn
  minimal_polynomial ... by exist!`.
- **Interface sketch:** `\minimal_polynomial(...)(T) : polynomial_space`.
- **Nearest wrong alternative:** A primitive trusted function named
  `minimal_polynomial` hides its defining annihilation/minimality properties;
  a proposition-only candidate leaves later zero and divisibility theorems
  carrying an avoidable witness.
- **Dependencies:** Polynomial degree and coefficient representation by
  `definition`; `p(T)` and the zero operator by `definition`; finite linear
  dependence, invariant range, and dimension by `existence`; degree comparison
  by `uniqueness`; unique existence by `selection`.
- **Downstream uses:** Eigenvalue classification, annihilating-polynomial
  divisibility, restrictions, invertibility, triangularization,
  diagonalizability, generalized eigenspaces, and Jordan form.
- **Allowable hole:** The source's induction on dimension may remain one named
  axiom while Chapter 2 finite-list exchange and restricted-operator
  infrastructure are unfinished. The selected function must still expose the
  exact candidate relation.

### Restriction to an invariant subspace

- **Ordinary meaning:** If `U` is invariant under `T`, the restriction sends
  each `u` in `U` to the same value `T(u)`, now regarded as an element of `U`.
- **Semantic role:** Callable construction whose codomain typing depends on an
  invariant-subspace proof.
- **Ideal Litex form:** A template-scoped `have fn restricted_operator` with
  the equality `restricted_operator(u)=T(u)` and operator codomain `U` under
  the inherited subspace vector-space structure.
- **Interface sketch:** `\restricted_operator(...,T,U)(u)`.
- **Nearest wrong alternative:** A relation `is_restriction(S,T,U)` without a
  selected callable map makes every theorem about `T|U` carry a fresh map.
- **Dependencies:** Invariant-subspace closure by `well_definedness`; inherited
  subspace operations and linearity by `law`.
- **Downstream uses:** Minimal polynomials of restrictions, triangularization
  by invariant flags, eigenspace restrictions, and induction on dimension.
- **Allowable hole:** The selected function may be trusted only at the
  dependent-codomain projection step; its pointwise equality must remain
  visible.

### Operator matrices and triangular form

- **Ordinary meaning:** Once one basis of `V` is fixed, an operator has a
  square matrix. Its diagonal is the ordered list `A(i,i)`, and it is upper
  triangular exactly when `A(i,j)=0` below the diagonal.
- **Semantic role:** Reused callable matrix construction, callable diagonal
  extraction, matrix relation, and existence relation over bases.
- **Ideal Litex form:** Specialize `matrix_of_linear_map` to one basis; define
  `have fn matrix_diagonal`; define `prop is_upper_triangular_matrix`; express
  “T has an upper-triangular matrix” by existence of a basis.
- **Interface sketch:** `$is_upper_triangular_matrix(s,scalars,n,A)`.
- **Nearest wrong alternative:** A second operator-matrix construction
  duplicates Chapter 3 coordinates; a selected triangularizing basis is not
  canonical.
- **Dependencies:** Matrix of a linear map and bases by `definition`;
  finite-list entries and scalar zero by `definition`.
- **Downstream uses:** Invariant flags, eigenvalues from the diagonal,
  triangularization, diagonalization, Schur form, and Jordan form.
- **Allowable hole:** Equivalence with invariant prefix spans and existence of
  triangularizing bases may remain source-facing proof boundaries while the
  matrix predicate and diagonal function remain checked.

### Diagonalization, eigenspaces, and Gershgorin disks

- **Ordinary meaning:** A diagonalizable operator has a diagonal matrix in
  some basis. Its eigenspace at `lambda` is `null(T-lambda I)`. Gershgorin
  disks are basis-dependent subsets centered at diagonal matrix entries with
  radii given by the off-diagonal row magnitudes.
- **Semantic role:** Matrix relation, operator relation, set-valued eigenspace,
  and indexed set-valued disk construction.
- **Ideal Litex form:** `prop is_diagonal_matrix`, `prop is_diagonalizable`,
  `have fn eigenspace`, and `have fn gershgorin_disk` after a callable finite
  radius construction.
- **Interface sketch:** `\eigenspace(...)(T,lambda)` and
  `\gershgorin_disk(...)(A,j,magnitude)`.
- **Nearest wrong alternative:** A selected eigenbasis is noncanonical; a
  predicate-only eigenspace or disk hides the sets needed by direct sums,
  restrictions, dimensions, and membership conclusions.
- **Dependencies:** Operator matrix and null space by `definition`; direct sums
  and dimension by `proof`; minimal-polynomial factorization by `proof`;
  finite real sums and scalar magnitude by `definition` and `well_definedness`.
- **Downstream uses:** Simultaneous diagonalization, spectral theorems,
  generalized eigenspaces, matrix-power calculations, and eigenvalue bounds.
- **Allowable hole:** Finite eigenspace-family dimension sums and Gershgorin's
  maximum-coordinate estimate may remain explicit proof debt; disk membership
  and eigenspaces must remain callable.

### Commuting operators and simultaneous forms

- **Ordinary meaning:** Two operators commute when their two composites are
  equal. Two square matrices commute by the analogous product equality. A
  common basis can then expose simultaneous diagonal or upper-triangular form.
- **Semantic role:** Relations on supplied operators or matrices, followed by
  existence relations over one shared basis.
- **Ideal Litex form:** `prop operators_commute`, `prop matrices_commute`,
  `prop have_common_diagonalizing_basis`, and `prop
  have_common_upper_triangular_basis`.
- **Interface sketch:** `$operators_commute(...,S,T)` and
  `$have_common_diagonalizing_basis(...,S,T)`.
- **Nearest wrong alternative:** Selecting a canonical common basis would add
  nonexistent mathematical uniqueness; defining commutation pointwise would
  duplicate the already callable composition operation.
- **Dependencies:** Linear-map composition and matrix multiplication by
  `definition`; matrices of products by `proof`; eigenspace invariance,
  restrictions, and diagonalization by `proof`.
- **Downstream uses:** Common eigenvectors, simultaneous triangularization,
  eigenvalues of sums and products, generalized eigenspaces, and spectral
  decomposition.
- **Allowable hole:** The induction that constructs a simultaneous triangular
  basis and the finite choice of eigenspace bases may remain named proof debt.
  Commutation itself and the shared-basis conclusions must remain explicit.

### Inner-product scalar geometry

- **Ordinary meaning:** Over `R` or `C`, inner-product formulas use scalar
  conjugation, absolute value, real part, and the embedding of real numbers
  into the scalar field.
- **Semantic role:** A bundled scalar-side structure attached to an existing
  `ScalarSystem`; it is not an inner product and does not mention vectors.
- **Ideal Litex form:** `struct InnerProductScalarGeometry<s,scalars>` with
  callable `conjugate`, `absolute_value`, `real_part`, and `real_embed` fields
  plus their field-compatible laws; provide the real and complex instances.
- **Interface sketch:** `@Geometry.conjugate(lambda)` and
  `@Geometry.absolute_value(lambda)`.
- **Nearest wrong alternative:** Passing four unrelated functions to every
  Chapter 6 and 7 declaration obscures which scalar identities are available;
  folding them into a vector-space structure assigns scalar data to the wrong
  object.
- **Dependencies:** `ScalarSystem` by `signature`; the concrete Chapter 4
  complex conjugate and absolute value by `definition`; their laws by `law`.
- **Downstream uses:** Inner-product positivity and conjugate symmetry, norms,
  Cauchy-Schwarz, orthonormality, adjoints, and normal operators.
- **Allowable hole:** The two concrete instances may remain selected trust
  boundaries until the real and complex scalar laws are packaged from Chapter
  4 without projection friction.

### Inner products, norms, and orthogonality

- **Ordinary meaning:** An inner product is positive definite, linear in its
  first slot, and conjugate symmetric. An inner-product space is a vector space
  equipped with one. The induced norm is the square root of `<v,v>`, and two
  vectors are orthogonal exactly when their inner product is zero.
- **Semantic role:** Relation on a candidate binary scalar-valued function;
  bundled equipped structure; callable norm and orthogonal-decomposition
  constructions; orthogonality relation.
- **Ideal Litex form:** `prop is_inner_product`, `struct InnerProductSpace`,
  `have fn norm`, `prop are_orthogonal`, and callable coefficient/remainder
  functions for Result 6.13.
- **Interface sketch:** `@Inner.inner(u,v)`, `\norm(...)(v)`, and
  `$are_orthogonal(...,u,v)`.
- **Nearest wrong alternative:** A predicate-only norm or a relation with a
  proposed decomposition output forces every inequality to carry avoidable
  witnesses; selecting a canonical inner product on an arbitrary vector space
  invents structure absent from the source.
- **Dependencies:** Scalar geometry and vector-space operations by
  `definition`; square-root and real order by `definition` and `proof`;
  conjugate symmetry and linearity by `law`.
- **Downstream uses:** Cauchy-Schwarz, triangle and parallelogram laws,
  orthonormal bases, Gram-Schmidt, orthogonal complements, projections, Riesz
  representation, and adjoints.
- **Allowable hole:** Square-root transport, equality cases, and generic scalar
  normalization may remain named theorem debt. The norm and the two pieces of
  the one-vector orthogonal decomposition must remain callable.

### Orthonormal bases, Gram-Schmidt, and Riesz representation

- **Ordinary meaning:** An orthonormal list has unit vectors with zero mutual
  inner products; an orthonormal basis is additionally a basis. Gram-Schmidt
  turns an independent list into an orthonormal list with the same prefix
  spans. Every finite-dimensional linear functional has one representing
  vector under the inner product.
- **Semantic role:** Relations on finite lists; an existence theorem over a
  finite construction trace; unique existence followed by a canonical
  selected Riesz representative.
- **Ideal Litex form:** `prop is_orthonormal`, `prop is_orthonormal_basis`,
  `prop is_gram_schmidt_trace`, prove the Riesz `exist!`, then `have fn
  riesz_representative ... by exist!`.
- **Interface sketch:** `$is_orthonormal(...,vectors)` and
  `\riesz_representative(...)(phi)`.
- **Nearest wrong alternative:** Selecting a canonical orthonormal basis is
  mathematically unjustified; exposing every Gram-Schmidt induction step as a
  named theorem bloats the API; selecting a Riesz vector before uniqueness
  hides the dependency needed by adjoints.
- **Dependencies:** Finite lists, linear combinations, spans, bases, norms,
  and orthogonality by `definition`; Gram-Schmidt by `proof`; Riesz existence
  by orthonormal coordinates and uniqueness by definiteness.
- **Downstream uses:** Orthonormal coordinates, Schur form, orthogonal
  complements and projections, adjoints, and the spectral theorem.
- **Allowable hole:** Finite vector-sum normalization and the Gram-Schmidt
  induction may remain one named proof boundary. The Riesz selector must expose
  its representing equation through a visible specification bridge.

### Orthogonal complements, projections, and pseudoinverses

- **Ordinary meaning:** `U^perp` is the set of vectors orthogonal to every
  member of `U`. Finite-dimensional `U` gives `V=U direct-sum U^perp`, hence a
  unique orthogonal projection. A linear map's pseudoinverse sends `w` to the
  unique vector in `(null T)^perp` mapped to the projection of `w` onto
  `range T`.
- **Semantic role:** Set-valued construction; pointwise unique selection for
  projection values; unique-existence relation for the pseudoinverse map.
- **Ideal Litex form:** `have fn orthogonal_complement`; prove the unique
  `U`-component of each `v`, then define `orthogonal_projection(v)` by
  pointwise `exist!`; prove linearity in the source projection-properties
  theorem. Prove/select `pseudoinverse` from its exact range/null
  characterization.
- **Interface sketch:** `\orthogonal_complement(...)(U)`,
  `\orthogonal_projection(...)(U)`, and `\pseudoinverse(...)(T)`.
- **Nearest wrong alternative:** A predicate-only complement hides the set;
  selecting a whole projection operator before defining its values reverses
  the source construction; directly trusting pseudoinverse hides its
  well-definedness; arbitrary complements lose the canonical geometry.
- **Dependencies:** Orthogonality by `definition`; finite direct sums by
  `existence` and `uniqueness`; null/range and inverse restrictions by `proof`.
- **Downstream uses:** Distance minimization, least-squares solutions,
  adjoints, positive operators, singular values, and polar decomposition.
- **Allowable hole:** The direct-sum construction and dependent restricted
  inverse may remain named proof boundaries. Both selected maps must keep an
  explicit specification bridge until selector elimination is automatic.

### Adjoints, conjugate transpose, self-adjointness, and normality

- **Ordinary meaning:** The adjoint `T* : W -> V` is the unique linear map
  satisfying `<T v,w>_W = <v,T* w>_V`. Conjugate transpose is its coordinate
  matrix operation in orthonormal bases. An operator is self-adjoint when
  `T=T*`, and normal when `T T*=T* T`.
- **Semantic role:** Canonically selected linear map; formula-defined matrix
  function; two operator relations.
- **Ideal Litex form:** Define `prop is_adjoint_of`, prove unique existence in
  the reverse linear-map carrier, then expose `have fn adjoint by exist!`.
  Define `conjugate_transpose` entrywise, `is_self_adjoint` by one function
  equality, and `is_normal` by one composition equality.
- **Interface sketch:** `$is_adjoint_of(...,T,S)`, `\adjoint(...)(T)`,
  `\conjugate_transpose(...)(A)`, `$is_self_adjoint(...,T)`, and
  `$is_normal(...,T)`.
- **Nearest wrong alternative:** A candidate-only adjoint predicate leaves no
  `T*` for later chapters; trusting an arbitrary map hides Riesz uniqueness;
  expanded norm conditions are characterizations of normality, not its
  definition; public real/imaginary-part helpers used only by Result 7.23
  would be proof-only API sprawl.
- **Dependencies:** Riesz representation by `existence/uniqueness`; assembly
  into a linear map by `proof`; scalar conjugation and matrix coordinates by
  `definition`; self-adjoint and normal consequences by `proof`.
- **Downstream uses:** Spectral theorems, positivity, square roots, unitary
  operators, singular values, polar decomposition, and operator norm.
- **Allowable hole:** Riesz-to-linear-map assembly remains one named
  construction boundary. The mathematical unique-existence statement is
  explicit, but the current verifier rejects `have fn ... by exist!` when its
  selected value belongs to the linear-map subtype. Thus `adjoint` keeps one
  typed direct trust and one visible spec bridge until subtype-valued
  parameterized selection works.

### Orthonormal spectral bases

- **Ordinary meaning:** A spectral basis is an orthonormal basis in which an
  operator has a diagonal matrix, equivalently an orthonormal basis consisting
  of eigenvectors. Over the reals this characterizes self-adjoint operators;
  over the complexes it characterizes normal operators.
- **Semantic role:** Two existential basis relations and two source-facing
  three-way equivalence theorems; no canonical basis is selected.
- **Ideal Litex form:** Use `prop has_orthonormal_diagonalizing_basis` and
  `prop has_orthonormal_eigenvector_basis`, then state each spectral theorem as
  two adjacent iff clauses so all three source conditions are genuinely
  equivalent.
- **Interface sketch:** `$has_orthonormal_diagonalizing_basis(...,T)`,
  `$has_orthonormal_eigenvector_basis(...,T)`, `real_spectral_theorem`, and
  `complex_spectral_theorem`.
- **Nearest wrong alternative:** Selecting a preferred eigenbasis invents
  noncanonical data; using only ordinary diagonalizability loses
  orthonormality; writing `A <=> B and C` is weaker than the source's three-way
  equivalence because it does not separately imply `B <=> C`.
- **Dependencies:** Real minimal-polynomial factorization and orthonormal
  triangularization by `proof` for the real theorem; Schur triangularization,
  the adjoint matrix bridge, and the normal norm equality by `proof` for the
  complex theorem.
- **Downstream uses:** Positive operators, square roots, isometries, singular
  values, polar decomposition, and operator-norm formulas.
- **Allowable hole:** The two spectral arguments may remain named proof
  boundaries until triangular-matrix coefficient elimination and the
  self-adjoint minimal-polynomial factorization route are checked.

### Positive operators and positive square roots

- **Ordinary meaning:** An operator is positive when it is self-adjoint and
  its quadratic form is nonnegative. A square root of `T` is an operator `R`
  with `R^2=T`; a positive operator has exactly one positive square root.
- **Semantic role:** Positivity and being a square root are relations. The
  positive square root is a canonical operator selected only after its
  existence and uniqueness theorem.
- **Ideal Litex form:** Define `prop is_positive_operator` and
  `prop is_square_root_of`; state the six conditions in Result 7.38 as
  adjacent iff clauses; prove `exist! R` for the positive square root and then
  expose `have fn positive_square_root by exist!`.
- **Interface sketch:** `$is_positive_operator(...,T)`,
  `$is_square_root_of(...,T,R)`, and `\positive_square_root(...)(T)`.
- **Nearest wrong alternative:** Selecting a spectral basis invents
  noncanonical data; selecting a square root before uniqueness permits the
  many nonpositive roots; expanding positivity into a repeated eigenbasis
  construction obscures its one quadratic-form condition.
- **Dependencies:** The spectral theorem and nonnegative scalar square roots
  give existence; spectral eigenvectors give uniqueness; the selected root's
  defining relation gives Result 7.43 in two mathematical moves.
- **Downstream uses:** Positive-definite operators, Cholesky factorization,
  singular values, polar decomposition, and operator-norm formulas.
- **Allowable hole:** The six-condition cycle and spectral uniqueness proof
  may remain named proof boundaries. The mathematical `exist!` statement is
  explicit, but the current verifier does not instantiate the subtype-valued
  selector in a real importing caller; one typed selection boundary and one
  specification bridge may remain until that works.

## Dependency map

Edge legend used below: `sig` = signature, `def` = definition, `law` =
structure law, `wd` = well-definedness, `ex` = existence, `uniq` = uniqueness,
`select` = canonical selection, `proof` = theorem dependency, and `trust` =
explicit axiom/trusted-source boundary.

```text
R ----def----> Complex ----law/wd----> complex ScalarSystem instance
|                                    /
+----checked laws----> real ScalarSystem instance ---> generic ScalarSystem
                                         |
FiniteList/finite_seq <---sig/def---------+
        |                                |
        +---def---> coordinate spaces <--law--- VectorSpace
                                             |
                       +---------------------+-------------------+
                       |                                         |
                  def/proof                                 sig/law
                       v                                         v
       subspace -> subspace sum -> direct sum             linear maps
                       |                                  /     |      \
                       |                                 /      |       \
                  def/proof                        null/range matrices  duals
                       v                              |       |          |
 linear combination -> span -> independence          |       |          |
                       \       /                      |       |          |
                        basis ----ex/uniq----> dimension       |          |
                           \____________________|______________/__________/
                                                |
                                                v
                            rank / isomorphism / product / quotient

ScalarSystem + FiniteList ----def----> polynomial representation
        polynomial representation --uniq/select--> degree
        degree + division + finite induction --proof--> factorization
        complex analytic minimum-modulus result --trust--> first FTA
        first FTA --proof--> complex and real factorization

linear maps(V,V) --def--> operators --def--> invariant subspaces
        |                         |
        +--def--> eigen-data -----+--proof--> restrictions/eigenspaces
        |
        +--def--> operator powers <---def--- identity/composition/inverse
                         |
polynomial representation + finite linear combinations
                         |
                         +--def/wd/uniq--> polynomial at operator
                                             |
                                             +--proof--> multiplicativity
                                             +--proof--> invariant null/range

monic + p(T)=0 + degree order --ex/uniq--> minimal-polynomial candidate
                                           |
                                           +--select--> minimal polynomial
                                           +--proof--> zeros/eigenvalues
                                           +--proof--> divisibility
invariant subspace --wd/law--> restricted operator --proof--> restriction minimal polynomial
operator + one basis --def--> square operator matrix --def--> diagonal/upper triangular
                                                    |
prefix spans --proof-------------------------------+--proof--> invariant flag

operator composition --def--> operator commutation --proof--> eigenspace invariance
matrix multiplication --def--> matrix commutation <---proof--- matrices of products
operator commutation + diagonalization --proof--> common diagonalizing basis
operator commutation + complex eigenvectors --proof--> common upper-triangular basis

ScalarSystem + conjugate/absolute-value/real-part --law--> inner-product scalar geometry
VectorSpace + scalar geometry + binary scalar function --law--> InnerProductSpace
InnerProductSpace --def--> norm + orthogonality --def--> one-vector orthogonal decomposition
orthogonal decomposition --proof--> Cauchy-Schwarz --proof--> triangle inequality
orthogonality + finite lists --def--> orthonormal list --proof--> Gram-Schmidt
orthonormal list + basis --def--> orthonormal basis --proof--> coordinates
orthonormal coordinates + linear functional --ex/uniq--> Riesz representative
orthogonality + subset --def--> orthogonal complement --proof--> direct decomposition
direct decomposition --ex/uniq--> orthogonal projection
null/range + orthogonal projection + restricted inverse --ex/uniq--> pseudoinverse
Riesz representative --ex/uniq+proof--> adjoint --def/proof--> self-adjoint / normal
adjoint + orthonormal coordinates --proof--> conjugate transpose matrix bridge
self-adjoint + real minimal-polynomial factors + orthonormal triangularization --proof--> real spectral theorem
normal + Schur + adjoint norm equality --proof--> complex spectral theorem
real/complex spectral theorem + nonnegative eigenvalues --ex--> positive square root
positive square-root spectral action --uniq/select--> positive square root
positive square root + inner-product definiteness --proof--> zero quadratic form criterion
```

Current trust boundaries have important downstream fan-out:

- the remaining selected complex/vector structure constructions feed almost
  every later construction, although generic scalar/vector laws now project
  without named bridge axioms;
- finite-list extensionality and exchange feed bases, dimension, rank, and
  finite polynomial representations;
- basis existence/uniqueness feeds all dimension and matrix-coordinate work;
- quotient well-definedness feeds the first isomorphism theorem; and
- the analytic FTA input feeds only the Chapter 4 factorization branch.

There is no intended mathematical cycle. Candidate relations precede selected
values: basis existence and length uniqueness precede `dimension`; inverse
existence and uniqueness precede `inverse_linear_map`; quotient equivalence and
representative independence precede quotient operations. Any implementation
that selects these objects before those edges are discharged is temporary
proof debt, not a different concept model.

## Intended build order

1. Keep the checked real scalar instance stable; finish the concrete complex
   scalar instance using the same explicit-operation pattern.
2. Check finite-list extensionality and coordinate/function vector spaces.
3. Finish inherited subspace structure, finite sums, and direct sums.
4. Finish the finite linear-combination fold, span, and independence.
5. Prove exchange/deletion, basis extraction/extension, basis-length
   uniqueness, and only then select dimension.
6. Construct pointwise linear-map operations and prove null/range subspace
   results plus the fundamental dimension theorem.
7. Construct matrices from basis coordinates; define row/column rank through
   span and dimension; derive matrix identities.
8. Select inverse maps from uniqueness, then construct product, quotient, and
   dual spaces with their well-defined operations.
9. In parallel after scalar and finite-list foundations stabilize, finish
   polynomial representation, degree, division, and algebraic factorization;
   keep the analytic FTA input as a separately visible source boundary.
10. Specialize linear maps to operators; define invariant subspaces and
    eigen-data; then construct powers and polynomial evaluation before the
    minimal-polynomial, triangularization, and diagonalization branches.
11. Define monicity, annihilation, and minimality as relations; prove the
    finite-dimensional unique-existence theorem before selecting the minimal
    polynomial, then build restriction results and parity consequences.
12. Reuse the Chapter 3 matrix construction for one-basis operator matrices;
    define diagonal and triangular predicates before proving their invariant-
    flag and minimal-polynomial characterizations.
13. Define operator and matrix commutation from their existing products; use
    eigenspace invariance and restrictions to construct common diagonal and
    upper-triangular bases without selecting either basis canonically.
14. Package the real/complex scalar geometry once, then define inner products,
    equipped inner-product spaces, norms, and orthogonality before proving the
    orthogonal decomposition, Cauchy-Schwarz, and norm identities.
15. Define orthonormality on finite lists; keep Gram-Schmidt as one finite trace
    and proof; derive orthonormal bases and coordinates; prove Riesz unique
    existence before selecting the representative used by adjoints.
16. Define orthogonal complements as sets; prove the finite direct
    decomposition before selecting projections; derive the restricted
    null-complement bijection before selecting pseudoinverses.
17. Define the adjoint relation from the two inner products; record Riesz
    unique existence and the current subtype-selection boundary. Then define
    conjugate transpose, self-adjointness, and normality before their spectral
    consequences.
18. Express orthonormal diagonalizing and eigenvector bases as existential
    relations. Prove the real spectral theorem through minimal-polynomial
    factorization and the complex theorem through Schur triangularization;
    never select a canonical spectral basis.
19. Define positivity and the square-root relation before stating their six
    equivalent conditions. Prove unique existence of the positive square root,
    select only that operator, and derive the zero-quadratic-form result from
    the selected root in the source's two moves.
This order follows the book through Chapters 1–3. Polynomial representation
is introduced in Section 2A but its main theorem branch is intentionally
resumed in Chapter 4 after the shared scalar/list foundations are stable.

## Interface decisions and permissible gaps

- Preserve `ScalarSystem` and `VectorSpace` as structures with callable
  fields; do not replace them with global operations or proposition-only
  wrappers.
- Preserve `FiniteList` for zero-inclusive source lists and `finite_seq` for
  positive coordinate spaces until a verified unification keeps both use
  cases.
- Preserve set-valued construction forms for span, null, range, subspace sum,
  quotient carrier, and annihilator.
- Define rank as dimension of a span; a bounded natural selector is only
  temporary implementation debt.
- Select dimension, inverses, quotient operations, bases, and dual maps only
  through visible existence, uniqueness, or well-definedness obligations.
- The first FTA may depend on an explicit analytic source boundary. Algebraic
  consequences such as division, repeated factor extraction, conjugate roots,
  and finite induction should not be hidden behind that boundary.
- Reuse the existing linear-map carrier for operators. Keep eigenvalues and
  eigenvectors relational, and keep operator powers and polynomial evaluation
  callable. Do not select canonical eigen-data.
- Select the minimal polynomial only from its exact least-degree monic
  annihilator relation. Its zeros, factors, and constant term are consequences,
  not fields folded into the definition.
- Source theorem identity and source order remain visible even when a theorem's
  checked proof eventually cites a broader reusable interface.
