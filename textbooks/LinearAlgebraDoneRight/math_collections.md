# Mathematical Collections

## Purpose and scope

This manual records the mathematical spine for the implemented Chapters 1–4
and the Section 5A operator layer
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
