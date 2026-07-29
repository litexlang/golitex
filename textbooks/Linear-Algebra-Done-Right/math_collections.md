# Mathematical Collections

## Purpose and scope

This manual records the mathematical spine for the published Chapters 1 and 2
of Sheldon Axler's *Linear Algebra Done Right*, fourth edition. The
repository-local transcript dated 9 May 2026 is authoritative. The module keeps
Sections 1A through 2C in pedagogical order and intentionally stops before
Section 3A.

The exhaustive source-item coverage inventory belongs in the paired
`scripts/linear_algebra_done_right/` workspace. This file records only the
concepts and intermediate nodes that determine later interfaces.

## Modeling conventions

- A scalar domain is a carrier `s` together with a `ScalarSystem<s>` structure;
  it is not a predicate on untyped values. The two source instances are `R`
  and the concrete pair carrier `Complex`.
- A vector space is a carrier `VSet` together with a
  `V &VectorSpace<s,VSet>` structure. The structure owns its
  `scalars &ScalarSystem<s>` field, so later
  mathematics receives scalar and vector operations from one coherent bundle.
  Candidate operations and laws may still be tested by a relation before the
  structure is constructed. A theorem, `prop`, or template that already owns
  `space` reads scalar operations through `space.scalars`; it does not repeat
  a separate scalar-system parameter.
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

- **Ordinary meaning:** `Complex` is `R x R` with coordinate arithmetic;
  `ScalarSystem` packages the zero, one, addition, negation, multiplication,
  inverse, and field laws used uniformly later.
- **Semantic role:** Carrier plus bundled structure.
- **Ideal Litex form:** `struct Complex`; callable `have fn` operations; and
  `struct ScalarSystem<s>` with checked real and complex instances.
- **Interface sketch:** `struct Complex: real_coord R; im R`, followed by
  `have complex_scalars &ScalarSystem<&Complex>`.
- **Nearest wrong alternative:** A predicate `is_complex(z)` or a bare global
  carrier `F` would not expose values and operations to later maps.
- **Dependencies:** `R` by `signature`; coordinate formulas by `definition`;
  inverse by `well_definedness` and `uniqueness`.
- **Downstream uses:** The vector-space and finite-dimensional interfaces in
  the published slice. Probe: apply `ScalarSystem.add(a,b)` and obtain a value
  in `s`.
- **Allowable hole:** None in the ideal interface. The pair field is named
  `real_coord` because native `re` is reserved for the builtin `C` carrier.
  The real instance is now
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
- **Downstream uses:** Linear combinations, independence, bases, and
  dimension.
- **Allowable hole:** Construction of the empty dependent entry map and general
  `FiniteList` extensionality are still explicit boundaries.

### Vector spaces

- **Ordinary meaning:** A carrier with vector zero, addition, scalar
  multiplication, and Axler's vector-space laws.
- **Semantic role:** Bundled structure; `is_vector_space` is the candidate-law
  relation corresponding to structure membership. The real and complex
  source-facing specializations are candidate-law relations: the real one
  identifies the bundled scalar system, while the complex one takes candidate
  vector operations and states the axioms with the callable complex operations.
- **Ideal Litex form:**
  `struct VectorSpace<s nonempty_set,VSet nonempty_set>` with directly declared
  `scalars &ScalarSystem<s>`, `zero`, `add`, and `smul` fields.
- **Interface sketch:** `V &VectorSpace<s,VSet>` followed by
  `V.add(u,v)` or `V.scalars.mul(a,b)`.
- **Nearest wrong alternative:** A proposition that hides the three operations
  cannot support ordinary vector expressions or structures inherited by a
  subspace, product, quotient, or function space.
- **Dependencies:** Scalar system by nested `field`; carrier and operations by
  `signature`.
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
- **Allowable hole:** The linear-combination recursion, its three finite-sum
  laws, and all exchange/deletion results remain explicit debt. Current
  verifier performance requires the typed selected `span_carrier` plus its
  equality bridge when a structural predicate would otherwise expand the
  recursive selector; this is a temporary kernel boundary, not a replacement
  for the concrete `span` construction.

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
- **Allowable hole:** The current interface shape is correct, but the
  exchange, extraction, extension, and basis-length theorems remain named
  axioms.

## Dependency map

~~~text
Complex and R
  -> ScalarSystem
  -> VectorSpace
  -> subspaces and direct sums
  -> finite linear combinations
  -> span and linear independence
  -> bases
  -> dimension
~~~

This order is also the export order across `chap1a` through `chap2c`. A future
publication that adds Section 3A should extend this manual before adding the
linear-map interfaces to the public manifest.
