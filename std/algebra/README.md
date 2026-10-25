# Algebra: groups, fields and vector spaces

This package exports `group`, `field`, `vector_space`, `finite_span`, `basis`, `dependence`, `span_reduction`, `basis_existence`, `exchange`, `basis_comparison`, `basis_extension` and `dimension`. It provides shared
group, field and vector-space definitions and checked source theorems for
finite combinations, bases, dependence, removal, basis existence and single-step
exchange, invariant finite basis length, ordered basis extension and guarded
finite dimension. Import it as
`Algebra` and use explicit paths such as `Algebra::group::Group`,
`Algebra::field::Field` and `Algebra::vector_space::VectorSpace`.
The former single-export `Algebra:::` shorthand is no longer available.

```ini
[import std]
Algebra = algebra

[export]
main = "./main.lit"
```

For checkout-local projects, `[import] Algebra = "../../std/algebra"` is an
alternative; adjust the path relative to the importing manifest.

## A group and a unique solution

The following complete consumer constructs the integer additive group and
proves that `3+x=7` has a unique integer solution:

```litex
have fn add(x,y Z) Z=x+y
have fn neg(x Z) Z=-x

forall x,y,z Z:
    add(add(x,y),z)=add(x,add(y,z))

forall x Z:
    add(0,x)=x
    add(x,0)=x
    add(neg(x),x)=0
    add(x,neg(x))=0

have integers &Algebra::group::Group<Z> = (add,0,neg)
release thm Algebra::group::left_equation_unique(Z,integers,3,7)
```

`Group<A nonempty_set>` contains `mul`, `one` and `inv`, together with
associativity and two-sided identity/inverse laws. The identity makes the
carrier nonempty; a one-element group is allowed. Commutativity is a separate
property. The general proofs do not assume it.

## Relations and construction

| Interface | Meaning |
| --- | --- |
| `$is_abelian(A,G)` | Multiplication is commutative |
| `$is_subgroup(A,G,S)` | The subset contains the identity and is closed under the ambient multiplication and inverse |
| `$is_homomorphism(A,G,B,H,f)` | The complete function `f` preserves multiplication |
| `$is_normal_subgroup(A,G,S)` | A subgroup closed under conjugation |
| `$has_trivial_kernel(A,G,B,H,f)` | Every element sent to `H.one` is `G.one` |
| `\kernel<A,B,H,f>` | The subset `{x A: f(x)=H.one}` |

Qualify these names with `Algebra::group` in a consumer. The kernel set can be
formed for any complete supplied map; its normality theorem requires a
homomorphism. `has_trivial_kernel` alone does not imply injectivity for an
arbitrary map.

## Theorem interfaces

| Call after `Algebra::group::` | Checked premises and result |
| --- | --- |
| `identity_unique(A,G,e)` | A left identity candidate equals `G.one` |
| `inverse_unique(A,G,a,b)` | `G.mul(b,a)=G.one` implies `b=G.inv(a)` |
| `left_cancel(A,G,a,b,c)` | Equal left products imply `b=c` |
| `right_cancel(A,G,a,b,c)` | Equal right products imply `b=c` |
| `left_equation_unique(A,G,a,b)` | Unique existence of `x` with `G.mul(a,x)=b` |
| `subgroup_intersection(A,G,S,T)` | Two subgroup premises give a subgroup intersection |
| `homomorphism_identity(A,G,B,H,f)` | A homomorphism preserves the identity |
| `homomorphism_inverse(A,G,B,H,f,x)` | A homomorphism preserves inverses |
| `abelian_subgroups_are_normal(A,G,S)` | An abelian-group premise and subgroup premise give normality |
| `kernel_is_normal(A,G,B,H,f)` | A homomorphism has a normal kernel |
| `trivial_kernel_implies_injective(A,G,B,H,f)` | Homomorphism and trivial-kernel premises give native injectivity |
| `injective_implies_trivial_kernel(A,G,B,H,f)` | An injective homomorphism has trivial kernel |

These are ordinary source proofs using native sets, functions, struct laws and
equality reasoning. This package adds no native objects or reserved theorem
names and contains no `trust`, `axiom` or `abstract_prop` declarations.
No Lean replay was performed for this module.

## Examples and scope

The [imported consumer](../../examples/algebra/groups/main.lit) exercises all
twelve theorem interfaces and the trivial group. The
[Heisenberg group](../../examples/algebra/groups/noncommutative/main.lit)
is noncommutative and still uses cancellation and kernel normality.
The [integer lecture](../../showcases/abstract_algebra/README.md) develops
multiples, doubling, translation and the zero map using these shared interfaces.

Run the focused positive, rejection and bundled-import checks with
`python3 examples/algebra/groups/check.py` from the repository root.
[math_collections.md](math_collections.md) explains the mathematical dependencies.
The group export does not include quotients or Lagrange's theorem.


## Fields and vector spaces

`Field<K nonempty_set>` contains `zero`, `one`, `add`, `neg`, `mul` and `inv`.
Its laws require distinct zero and one, commutative addition/multiplication,
associativity, distribution and the identity/inverse laws. The inverse has the
guarded domain `fn(x K: x != zero) K`; applying it at zero is not well-defined.

`VectorSpace<K,field,V>` contains `zero`, `add` and `smul`, with the vector-space
laws over the supplied field. Additive inverses exist; their uniqueness is a
theorem. The carrier may be a singleton, so the zero-dimensional space is allowed.
There is no implicit ring/field coercion hierarchy.

Qualify the following interfaces with `Algebra::vector_space`:

| Interface | Meaning |
| --- | --- |
| `$is_subspace(K,F,V,X,U)` | `U power_set(V)` contains vector zero and is closed under ambient addition and scalar multiplication |
| `$is_linear_map(K,F,V,X,W,Y,T)` | The complete map `T fn(x V) W` is additive and homogeneous between spaces over `F` |
| `\identity<V>` | Identity map on `V` |
| `\zero_map<V,W,z>` | Constant map with value `z W`; linearity requires `z=Y.zero` |
| `\map_compose<U,V,W>(S,T)` | Composition `S(T(u))` |

Kernels and images use the native sets `preimage(T,Y.zero)` and `fn_range(T)`.
No separate kernel or image selector is introduced.

| Theorem after `Algebra::vector_space::` | Result and required premises |
| --- | --- |
| `additive_identity_unique(K,F,V,X,e)` | A left additive identity equals `X.zero` |
| `additive_inverse_exists_unique(K,F,V,X,x)` | Unique `y` with `X.add(x,y)=X.zero` |
| `zero_scalar_times_vector(K,F,V,X,x)` | `X.smul(F.zero,x)=X.zero` |
| `scalar_times_zero(K,F,V,X,a)` | `X.smul(a,X.zero)=X.zero` |
| `linear_map_zero(K,F,V,X,W,Y,T)` | A linear map preserves zero |
| `identity_linear(K,F,V,X)` | Identity is linear |
| `zero_map_linear(K,F,V,X,W,Y)` | The constant map at `Y.zero` is linear |
| `composition_linear(K,F,U,X,V,Y,W,Z,T,S)` | A composite of two supplied linear maps is linear |
| `kernel_is_subspace(K,F,V,X,W,Y,T)` | A linear map's kernel is a subspace of its source |
| `range_is_subspace(K,F,V,X,W,Y,T)` | A linear map's image is a subspace of its target |
| `injective_has_zero_kernel(K,F,V,X,W,Y,T)` | An injective linear map has kernel `{X.zero}` |
| `zero_kernel_is_injective(K,F,V,X,W,Y,T)` | A linear map with kernel `{X.zero}` is injective |

The following complete consumer forwards the injectivity criterion. It uses
no dimension assumption:

```litex
thm injectivity_from_kernel:
    ? forall K nonempty_set, F &Algebra::field::Field<K>, V nonempty_set, X &Algebra::vector_space::VectorSpace<K,F,V>, W nonempty_set, Y &Algebra::vector_space::VectorSpace<K,F,W>, T fn(x V) W:
        $Algebra::vector_space::is_linear_map(K,F,V,X,W,Y,T)
        preimage(T,Y.zero)={X.zero}
        =>:
            $injective(V,W,T)
    by thm Algebra::vector_space::zero_kernel_is_injective(K,F,V,X,W,Y,T) => $injective(V,W,T)
```

The [scalar-line consumer](../../examples/algebra/vector_spaces/main.lit)
constructs the real field and real vector space, verifies doubling is linear,
computes its zero kernel and calls all twelve theorem interfaces. The
[singleton consumer](../../examples/algebra/vector_spaces/zero_dimensional/main.lit)
checks the allowed zero-dimensional case. The
[linear-algebra lecture](../../showcases/linear_algebra/README.md) imports these
foundations and retains the real plane, span, basis and projection developments.

Run `python3 examples/algebra/vector_spaces/check.py` for the focused positive,
rejection and installed-import checks. Finite basis existence is supplied by
the basis_existence export below. Dimension invariance, a general dimension
function, ring hierarchies and quotients remain outside these shared exports. No additional native rules, source trust or Lean replay
are supplied by this increment.


## Finite combinations and span

`Algebra::finite_span` provides finite ordered linear combinations and their
spans over any supplied Field/VectorSpace. Coefficient and vector lists have
exact length `n N` and indices `1..n`; a partial-sum function uses `0..n` and
starts at vector zero. Empty and repeated lists are allowed.

| Interface after `Algebra::finite_span::` | Role |
| --- | --- |
| `$is_partial_sum(K,F,V,X,n,c,v,s)` | `s(0)=X.zero` and the coefficient-scaled recurrence |
| `$has_linear_combination_value(K,F,V,X,n,c,v,x)` | A partial-sum trace ends at candidate `x` |
| `$is_linear_combination(K,F,V,X,n,x,v)` | Some coefficient list produces `x` |
| `\linear_combination<K,F,V,X,n>(c,v)` | Value selected after existence and uniqueness are proved |
| `\span<K,F,V,X,n,v>` | Subset of V consisting of the list's linear combinations |
| `$spans(K,F,V,X,n,v)` | That span equals V |
| `\zero_coefficients<K,F,n>` | Length-n zero coefficient list |
| `\add_coefficients<K,F,n>(c,d)` | Pointwise coefficient addition |
| `\neg_coefficients<K,F,n>(c)` | Pointwise coefficient negation |
| `\smul_coefficients<K,F,n>(a,c)` | Pointwise coefficient scaling |
| `\map_vectors<V,W,n>(T,v)` | Length-n list of the complete map's values |

The 26 promoted source theorems retain their statements and proofs:

- `linear_combination_exists`, `linear_combination_exists_unique`,
  `partial_sum_determines_combination`, `empty_linear_combination`;
- `vector_add_regroup`, `scalar_partial_trace_step`;
- `zero_coefficients_entry`, `add_coefficients_entry`, `neg_coefficients_entry`,
  `smul_coefficients_entry`;
- `zero_coefficient_contribution`, `zero_coefficients_is_partial_sum`,
  `zero_coefficients_has_zero_value`, `linear_combination_zero_coefficients`;
- `add_coefficient_contribution`, `add_coefficients_is_partial_sum`,
  `linear_combination_add_coefficients`;
- `smul_coefficient_contribution`, `smul_trace_step`,
  `smul_coefficients_is_partial_sum`, `linear_combination_smul_coefficients`;
- `span_zero_member`, `span_add_closed`, `span_smul_closed`, `span_is_subspace`;
- `linear_map_preserves_combination`.

Two additional source theorems publish definition consequences across imports.
`zero_coefficients_carrier(K,F,n)` exposes the zero list's exact finite_seq
carrier before passing it into another function. `linear_combination_has_value`
uses `(K,F,V,X,n,c,v)` and exposes the selected value's defining candidate
relation. These are checked consequences, not new assumptions. For example,
the following complete consumer checks the empty combination after importing
`Algebra` with the manifest above:

```litex
claim:
    ? forall K nonempty_set,F &Algebra::field::Field<K>,V nonempty_set,X &Algebra::vector_space::VectorSpace<K,F,V>,c finite_seq(K,0),v finite_seq(V,0):
        \Algebra::finite_span::linear_combination<K,F,V,X,0>(c,v)=X.zero
    release thm Algebra::finite_span::empty_linear_combination(K,F,V,X,c,v)
```

The [independent consumer](../../examples/algebra/finite_span/main.lit) computes
`2*1+3*4=14` through a verified trace and calls the imported span-subspace theorem.
[Empty/repeated lists](../../examples/algebra/finite_span/empty.lit), a
[singleton space](../../examples/algebra/finite_span/zero_dimensional/main.lit)
and [the 28 original theorem contracts](../../examples/algebra/finite_span/contracts.lit)
are independently checked. The interface-contract claims test imports and exact
premises; they are not additional mathematical results.

Run `python3 examples/algebra/finite_span/check.py` for positive sources, seven
final-statement rejection controls, actual installed-library discovery and
package/WiX inventory equality. The [lecture](../../showcases/linear_algebra/README.md)
now imports this foundation while retaining independence, basis and concrete
coordinate proofs. General basis extension/exchange, dimension and rank-nullity
are still outside this export. No native rule, trust or Lean replay is added.


## Independence, bases and coordinates

`Algebra::basis` shares the lecture's ten relations: `has_only_zero_coefficients`,
`is_linearly_independent`, `is_basis`, `is_finite_dimensional`, `has_basis_length`,
`is_prefix_of_length`, `is_list_with_index_removed`, `is_linearly_dependent`,
`has_nontrivial_dependence_coefficients`, and `is_largest_nonzero_coefficient_index`.
The field/vector-space parameters and exact finite list lengths are preserved.
A basis is an independent spanning list; `has_basis_length` states existence of
a basis of the supplied length, and does not select a general dimension.

The six promoted theorem interfaces are `prefix_exists`, `remove_index_exists`,
`dependent_has_nontrivial_coefficients`, `largest_nonzero_index_length_two`,
`dependence_lemma_length_two` and `span_of_dependent_pair_reduces`. The last
three keep their stated length-two restrictions. They are not general exchange
theorems.

The new general interfaces use arbitrary finite `n N`:

| Interface | Checked contract |
| --- | --- |
| `independent_combination_coefficients_unique(K,F,V,X,n,v,c,d)` | Independence and equal selected combination values imply c=d |
| `basis_representation_exists_unique(K,F,V,X,n,v,x)` | A basis gives exactly one coefficient list representing x |
| `\basis_coordinates<K,F,V,X,n,v>(x)` | Selected coefficient list; forming the template requires the actual basis proposition |
| `basis_coordinates_has_value(K,F,V,X,n,v,x)` | The selected coordinates represent x |
| `basis_coordinates_unique(K,F,V,X,n,v,x,c)` | A supplied representing coefficient list equals those coordinates |
| `basis_coordinates_of_combination(K,F,V,X,n,v,c)` | Coordinates recover c from its combination in that basis |
| `basis_is_finite_dimensional(K,F,V,X,n,v)` | A supplied basis provides a finite spanning list |

All calls except the first theorem require `$is_basis(K,F,V,X,n,v)`.
The first requires `$is_linearly_independent(...)` instead. The parameter and
mathematical contract of `basis_coordinates` is fixed; it is not selected by
argument count or scalar/vector type. Empty bases are allowed for the zero space.
The selector is introduced only after general existence and uniqueness proofs.

The following complete imported consumer forwards the general existence/uniqueness
result; it does not assume the field is R or the basis has length two:

```litex
claim:
    ? forall K nonempty_set,F &Algebra::field::Field<K>,V nonempty_set,X &Algebra::vector_space::VectorSpace<K,F,V>,n N,v finite_seq(V,n),x V:
        $Algebra::basis::is_basis(K,F,V,X,n,v)
        =>:
            exist! c finite_seq(K,n) st {$Algebra::finite_span::has_linear_combination_value(K,F,V,X,n,c,v,x)}
    release thm Algebra::basis::basis_representation_exists_unique(K,F,V,X,n,v,x)
```

The [real-line consumer](../../examples/algebra/basis/main.lit) constructs the
unit basis and computes its coordinate of 7. The
[zero-space consumer](../../examples/algebra/basis/zero_dimensional/main.lit)
constructs the empty basis and obtains an empty coordinate list. All twelve
theorem interfaces are exercised by [generic contracts](../../examples/algebra/basis/contracts.lit).
Run `python3 examples/algebra/basis/check.py` for strict sources, seven precise
rejection controls, real installed imports and std/WiX inventory equality.

The [lecture](../../showcases/linear_algebra/README.md) imports these shared
relations/proofs and retains concrete plane calculations. The basis_existence
export below proves finite basis existence; exchange and basis_comparison
supply single-step exchange and invariant finite basis length. The later basis_extension, dimension and linear_dimension exports provide
ordered extension, selected finite dimension and general rank-nullity.
There are no new native rules or source trust assumptions.


## General finite dependence

`Algebra::dependence` proves the dependence lemma for every finite length
`n N` over a supplied field and vector space. A dependent list has an index
`k N+`, a length `m=k-1`, and its preceding prefix such that `vectors(k)`
belongs to the span of that prefix. The empty case is vacuous because the
empty list is independent. Length-one zero lists and repeated lists are allowed.

The six source theorems have fixed contracts:

| Theorem | Parameters and result |
| --- | --- |
| `largest_nonzero_index_exists` | `(K,F,n,c)`, `n N+`, not all coefficients zero: a largest nonzero coefficient index exists |
| `empty_list_is_independent` | `(K,F,V,X,v)`, `v finite_seq(V,0)`: independence |
| `partial_sum_prefix` | `(K,F,V,X,n,c,v,s,m,pc,pv,ps)`: supplied prefixes and pointwise restriction `ps(j)=s(j)` on `0..m` give the restricted partial-sum relation |
| `partial_sum_zero_tail` | `(K,F,V,X,n,c,v,s,k)`: a partial-sum trace and zero coefficients after `k` give `s(n)=s(k)` |
| `vector_zero_sum_solve` | `(K,F,V,X,a,p,v)`: `a!=F.zero` and `X.add(p,X.smul(a,v))=X.zero` give `v=X.smul(F.neg(F.inv(a)),p)` |
| `dependence_lemma` | `(K,F,V,X,n,v)`: dependence gives a vector in the span of its preceding prefix |

For the prefix theorem, `m N`, `m<=n`, coefficient/vector lists have the
declared exact lengths, and `ps fn(j closed_range(0,m)) V` is supplied by
the caller. No default trace or inverse at scalar zero is selected.

With the import manifest above, this complete generic consumer forwards the
general result:

```litex
claim:
    ? forall K nonempty_set,F &Algebra::field::Field<K>,V nonempty_set,X &Algebra::vector_space::VectorSpace<K,F,V>,n N,v finite_seq(V,n):
        $Algebra::basis::is_linearly_dependent(K,F,V,X,n,v)
        =>:
            exist k N+,m N,p finite_seq(V,m) st {k<=n,m=k-1,$Algebra::basis::is_prefix_of_length(V,n,m,v,p),v(k) $in \Algebra::finite_span::span<K,F,V,X,m,p>}
    release thm Algebra::dependence::dependence_lemma(K,F,V,X,n,v)
```

The [length-three consumer](../../examples/algebra/dependence/main.lit)
checks coefficients `(1,1,-1)` on `(1,2,3)`, then obtains the imported
lemma's prefix witness. [Boundary cases](../../examples/algebra/dependence/boundaries/main.lit)
check the empty list and singleton zero vector. The former length-two
interfaces remain available with their existing contracts.

Run `python3 examples/algebra/dependence/check.py` for strict source and import
checks, nine final-statement rejection controls, and both installed-library
layouts. The span_reduction and basis_existence exports below supply general
removal and finite basis existence. The basis_comparison export below proves invariant
finite basis length.
The later basis_extension and dimension exports supply ordered extension and
a guarded finite dimension value. The linear_dimension export below now proves general rank-nullity.


## Span minimality and redundant-vector removal

The span_reduction export supplies seven checked source theorems:

| Theorem after Algebra::span_reduction:: | Fixed contract |
| --- | --- |
| weighted_combination_in_subspace(K,F,V,X,n,c,v,x,U) | Subspace U, membership of every weighted contribution and a supplied combination value imply x belongs to U |
| linear_combination_in_subspace(K,F,V,X,n,c,v,x,U) | A supplied value relation, subspace U and membership of every generator imply x belongs to U |
| span_contains_generator(K,F,V,X,n,v,j) | n N, j N+ and j<=n imply v(j) belongs to the list's span |
| span_subset_subspace(K,F,V,X,n,v,U) | A subspace containing every generator contains the span |
| span_inclusion_from_generators(K,F,V,X,n,v,m,w) | Every generator in span(w) implies span(v) is a subset of span(w) |
| remove_redundant_vector_preserves_span(K,F,V,X,n,v,k,r) | n N+, the removed-index relation and v(k) in span(r) imply equal spans |
| dependent_list_has_span_preserving_removal(K,F,V,X,n,v) | A dependent positive-length list has an index and remaining length-(n-1) list with the same span |

All lists retain their exact finite_seq carriers. The closure and inclusion results admit
empty lists where their premises make sense. Removal requires positive n and
uses the existing is_list_with_index_removed relation, including its bound
k<=n. The deleted vector's membership is a required hypothesis of the explicit
removal criterion. The dependence theorem proves that some such index exists.

For example, with the import manifest above, this complete consumer exposes
span minimality over a supplied subspace:

```litex
claim:
    ? forall K nonempty_set,F &Algebra::field::Field<K>,V nonempty_set,X &Algebra::vector_space::VectorSpace<K,F,V>,n N,v finite_seq(V,n),U power_set(V):
        $Algebra::vector_space::is_subspace(K,F,V,X,U)
        forall j N+:
            j<=n
            =>:
                v(j) $in U
        =>:
            \Algebra::finite_span::span<K,F,V,X,n,v> $subset U
    by thm Algebra::span_reduction::span_subset_subspace(K,F,V,X,n,v,U) => \Algebra::finite_span::span<K,F,V,X,n,v> $subset U
```

The [concrete consumer](../../examples/algebra/span_reduction/main.lit) checks
(1,2,3) with deletion at each of its three indices, and obtains a deletion
witness from the general dependence theorem. It reuses the earlier real-field
data but proves the actual premises it consumes. The
[boundary consumer](../../examples/algebra/span_reduction/boundaries/main.lit)
deletes the singleton zero vector and checks empty-span minimality.
The existing generic contracts cover the six original interfaces; the exchange boundary consumer also uses weighted closure.

Run python3 examples/algebra/span_reduction/check.py for strict sources,
nine final-statement rejection controls, installed-library discovery and
std/WiX inventory equality. These results add no native operations, source
trust or scalar ordering. The basis_existence export below supplies finite
basis extraction; basis_comparison below adds length comparison and invariance.
The dimension and linear_dimension exports below now provide dimension
selection and rank-nullity.


## Finite spanning lists contain bases

Algebra::basis_existence supplies three source theorems:

| Theorem | Fixed parameters and result |
| --- | --- |
| removed_list_range_subset(V,n,v,k,r) | n N+, exact removed-list relation: fn_range(r) is a subset of fn_range(v) |
| spanning_list_has_basis_of_bounded_length(K,F,V,X,n,v) | n N and spanning: some m<=n and basis b of length m, with fn_range(b) a subset of fn_range(v) |
| finite_dimensional_has_basis(K,F,V,X) | The existing finite-dimensional premise implies existence of n N and a basis list of length n |

The extraction result admits empty generating lists. The removed-range helper
requires positive n because its remaining list has length n-1. Range inclusion
certifies values from the original generators; no order-preserving index map,
unique basis or strictly shorter output is promised. The final theorem together
with basis::basis_is_finite_dimensional gives both directions between finite
spanning-list existence and finite basis existence.

With the import manifest above, this complete consumer forwards finite basis
existence:

```litex
claim:
    ? forall K nonempty_set,F &Algebra::field::Field<K>,V nonempty_set,X &Algebra::vector_space::VectorSpace<K,F,V>:
        $Algebra::basis::is_finite_dimensional(K,F,V,X)
        =>:
            exist n N,b finite_seq(V,n) st {$Algebra::basis::is_basis(K,F,V,X,n,b)}
    release thm Algebra::basis_existence::finite_dimensional_has_basis(K,F,V,X)
```

The [imported consumer](../../examples/algebra/basis_existence/main.lit) extracts
a basis from (1,2,3) on the real line, then uses its unique-coordinate interface.
The [empty boundary](../../examples/algebra/basis_existence/boundaries/main.lit)
obtains a length-zero basis of the singleton zero space. Both prove the
premises they consume; they do not rely on a producer's anonymous facts.

Run python3 examples/algebra/basis_existence/check.py for positive/generic/
boundary sources, nine precise rejection controls, actual installed-library
discovery and std/WiX equality. This export has no source trust and adds no
native operation, public predicate, default basis choice or dimension function.
The basis_comparison export below supplies finite length comparison and
basis-length invariance. The later basis_extension and dimension exports supply ordered extension and
a guarded dimension value. The linear_dimension export below now proves general rank-nullity.


## Single-step exchange

The finite_span theorem single_coefficient_linear_combination(K,F,V,X,n,c,v,k)
computes a combination with every coefficient except k zero as X.smul(c(k),v(k)).
Here n is natural, k is positive and k<=n. The selected coefficient may be zero.
The span_reduction theorem weighted_combination_in_subspace needs membership
of the weighted contributions, so generators with zero coefficient need not
belong to the subspace.

The exchange export has one relation and six source theorems:

| Interface after Algebra::exchange:: | Fixed contract |
| --- | --- |
| is_list_with_index_replaced(V,n,v,k,u,w) | n N; v,w finite_seq(V,n); k closed_range(1,n); u V. Entry k is u and every other entry agrees with v |
| replacement_list_exists(V,n,v,k,u) | A legal supplied index has a replacement-list witness |
| subspace_additive_cancellation(K,F,V,X,U,x,y) | Subspace U, x in U and x+y in U imply y in U |
| subspace_nonzero_scalar_cancellation(K,F,V,X,U,a,x) | Subspace U, a!=F.zero and a*x in U imply x in U |
| exchange_by_nonzero_coefficient(K,F,V,X,n,c,v,u,k,w) | Supplied combination value u, c(k)!=F.zero and the replacement relation imply equal spans |
| combination_outside_subspace_has_nonzero_term(K,F,V,X,n,c,v,u,U) | A combination outside a supplied subspace has an index with nonzero coefficient and generator outside that subspace |
| nonzero_span_member_can_replace_generator(K,F,V,X,n,v,u) | u in span(v) and u!=X.zero give a legal index and replacement list with equal span |

All field/vector-space structures are supplied; scalar ordering is unnecessary.
There is no selected replacement function. The relation puts index legality in
its parameter domain, so an empty list has no replacement index. The explicit
exchange criterion can apply to u=X.zero; the nonzero-vector hypothesis belongs
to the existential corollary, where it guarantees a usable coefficient.

With the import manifest above, this complete consumer calls the criterion:

```litex
claim:
    ? forall K nonempty_set,F &Algebra::field::Field<K>,V nonempty_set,X &Algebra::vector_space::VectorSpace<K,F,V>,n N,c finite_seq(K,n),v finite_seq(V,n),u V,k closed_range(1,n),w finite_seq(V,n):
        $Algebra::finite_span::has_linear_combination_value(K,F,V,X,n,c,v,u)
        c(k)!=F.zero
        $Algebra::exchange::is_list_with_index_replaced(V,n,v,k,u,w)
        =>:
            \Algebra::finite_span::span<K,F,V,X,n,v> = \Algebra::finite_span::span<K,F,V,X,n,w>
    by thm Algebra::exchange::exchange_by_nonzero_coefficient(K,F,V,X,n,c,v,u,k,w) => \Algebra::finite_span::span<K,F,V,X,n,v> = \Algebra::finite_span::span<K,F,V,X,n,w>
```

The [real-plane consumer](../../examples/algebra/exchange/main.lit) checks
(e1,e2)->(e1+e2,e2), using coefficients (1,1), and obtains a further replacement
witness from the nonzero-member corollary. A concrete control tries replacing
index 2 in e1=1*e1+0*e2 and is rejected at the required nonzero coefficient.
The [boundaries](../../examples/algebra/exchange/boundaries/main.lit) permit a
zero-valued exchange with a nonzero coefficient and check empty weighted closure.

Run python3 examples/algebra/exchange/check.py for strict sources, arbitrary-field
contracts, ten final-statement controls, installed imports and std/WiX equality.
These source proofs introduce no native rule, assumption or operation overload.
The basis_comparison export below proves independent-versus-spanning length
comparison and equal finite basis lengths. The later basis_extension and dimension exports supply ordered extension and
a guarded dimension value; linear_dimension below proves general rank-nullity.


## Comparison and unique finite basis length

The basis_comparison export supplies six source theorems:

| Call after Algebra::basis_comparison:: | Exact mathematical contract |
| --- | --- |
| independent_vector_outside_prefix_span(K,F,V,X,m,v,p,prefix) | Independent v, the supplied prefix relation and p<m imply v(p+1) is outside span(prefix) |
| independent_list_in_span_length_bound(K,F,V,X,m,u,n,v) | Independent u with every entry in span(v) implies m<=n |
| independent_spanning_length_bound(K,F,V,X,m,u,n,v) | Independent u and v spanning V imply m<=n |
| finite_bases_have_equal_length(K,F,V,X,m,u,n,v) | Two supplied finite bases of the same space imply m=n |
| basis_length_unique(K,F,V,X,m,n) | The existing has_basis_length relation at m and n implies m=n |
| finite_dimensional_has_unique_basis_length(K,F,V,X) | Finite dimensionality implies exist! n N with has_basis_length(K,F,V,X,n) |

K and V are nonempty and F/X are supplied Field/VectorSpace structures.
All lengths are natural, including zero; the proper-prefix theorem separately
requires p<m. The first comparison needs containment in a finite span rather
than spanning the whole ambient space. No scalar ordering is assumed.

A finite exchange proof embeds successive independent vectors at distinct
positions in a generating list, preserving its span. A finite injection bounds
the independent length. Two proof-local props hold the embedding certificate
and guarded induction assertion; neither is a public predicate or operation.

With the import manifest above, this complete consumer compares two bases:

```litex
claim:
    ? forall K nonempty_set,F &Algebra::field::Field<K>,V nonempty_set,X &Algebra::vector_space::VectorSpace<K,F,V>,m N,u finite_seq(V,m),n N,v finite_seq(V,n):
        $Algebra::basis::is_basis(K,F,V,X,m,u)
        $Algebra::basis::is_basis(K,F,V,X,n,v)
        =>:
            m=n
    by thm Algebra::basis_comparison::finite_bases_have_equal_length(K,F,V,X,m,u,n,v) => m=n
```

The [imported real example](../../examples/algebra/basis_comparison/main.lit)
extracts a basis from (1,2,3) and proves that its initially unspecified length
equals the unit basis length 1. It also obtains the unique natural basis length.
The [zero-space boundary](../../examples/algebra/basis_comparison/boundaries/main.lit)
checks that the unique length is 0.

Run python3 examples/algebra/basis_comparison/check.py for strict sources, all six
generic calls, ten precise rejection controls, installed-library discovery and
std/WiX equality. The comparison export adds no source trust, native rule,
operation overload or selected dimension. The basis_extension and dimension
exports below provide ordered extension and a public guarded dimension value. The linear_dimension export below proves general rank-nullity. Further
undergraduate course lanes remain active.


## Ordered basis extension

Algebra::basis_extension supplies a finite-list construction and four theorems:

| Interface | Fixed contract |
| --- | --- |
| \append_vector<V,m,u,x> | V nonempty, m N, u finite_seq(V,m), x V: a list of length m+1, agreeing with u through m and equal to x at m+1 |
| append_outside_span_is_independent(K,F,V,X,m,u,x) | Independent u and x outside span(u) imply that the appended list is independent |
| independent_list_with_basis_length_spans(K,F,V,X,n,u) | has_basis_length at n and independent u of length n imply spanning |
| spanning_list_with_basis_length_is_independent(K,F,V,X,n,u) | has_basis_length at n and spanning u of length n imply independence |
| independent_list_extends_to_basis(K,F,V,X,m,u) | Finite dimensionality and independent u imply existence of a basis retaining u as its ordered prefix |

The append construction is a template instance whose value is the complete
finite sequence. Apply it to an index only in closed_range(1,m+1). Empty input
lists are permitted. This single spelling has no arity/type dispatch.

The extension certificate is is_prefix_of_length(V,n,m,extended,u), with
extended the longer list. It preserves the original order and every original
entry, rather than only inclusion of vector ranges. Its witness is existential;
there is no default selected basis.

With the import manifest above, this complete consumer obtains such a basis:

```litex
claim:
    ? forall K nonempty_set,F &Algebra::field::Field<K>,V nonempty_set,X &Algebra::vector_space::VectorSpace<K,F,V>,m N,u finite_seq(V,m):
        $Algebra::basis::is_finite_dimensional(K,F,V,X)
        $Algebra::basis::is_linearly_independent(K,F,V,X,m,u)
        =>:
            exist n N,b finite_seq(V,n) st {$Algebra::basis::is_basis(K,F,V,X,n,b),$Algebra::basis::is_prefix_of_length(V,n,m,b,u)}
    release thm Algebra::basis_extension::independent_list_extends_to_basis(K,F,V,X,m,u)
```

Appending a vector outside the current span preserves independence. At the
known basis length, an independent list must span, because one more append
would violate the established length bound. Induction on the remaining
natural length gives the ordered extension. One proof-local prop captures
the deficit invariant; no public witness-package predicate is added.

## A guarded finite dimension value

The exact public value call is:

    \Algebra::dimension::finite_dimension<K,F,V>(X)

K/F/V are the fixed template parameters; X is the single supplied VectorSpace
argument. Its domain requires a checked
is_finite_dimensional(K,F,V,X), and its result is N. The value is selected from
the already proved unique has_basis_length relation. It is not a native builtin
and has no formula body or basis-choice argument. The provisional ordinary
four-argument spelling was never declared; it is not another supported API.

All value theorems keep the finite-dimensional domain explicit. A known finite
basis or finite spanning list can supply that domain evidence through the
existing basis/finite-dimensional interfaces before forming the partial value.

| Theorem after Algebra::dimension:: | Further premises and result |
| --- | --- |
| finite_dimension_has_basis_length(K,F,V,X) | The selected value satisfies has_basis_length |
| finite_dimension_of_basis(K,F,V,X,n,u) | A supplied basis has length equal to the selected value |
| independent_length_le_dimension(K,F,V,X,m,u) | Independence implies m<=finite_dimension |
| dimension_le_spanning_length(K,F,V,X,n,u) | Spanning implies finite_dimension<=n |
| independent_dimension_list_is_basis(K,F,V,X,n,u) | Independence and n=finite_dimension imply basis |
| spanning_dimension_list_is_basis(K,F,V,X,n,u) | Spanning and n=finite_dimension imply basis |

For example, this complete consumer checks the value against a supplied basis:

```litex
claim:
    ? forall K nonempty_set,F &Algebra::field::Field<K>,V nonempty_set,X &Algebra::vector_space::VectorSpace<K,F,V>,n N,u finite_seq(V,n):
        $Algebra::basis::is_finite_dimensional(K,F,V,X)
        $Algebra::basis::is_basis(K,F,V,X,n,u)
        =>:
            \Algebra::dimension::finite_dimension<K,F,V>(X)=n
    by thm Algebra::dimension::finite_dimension_of_basis(K,F,V,X,n,u) => \Algebra::dimension::finite_dimension<K,F,V>(X)=n
```

The [real-plane consumer](../../examples/algebra/dimension_extension/main.lit)
computes dimension 2, extends (e1) to a length-2 basis whose first entry remains
e1, and uses the new basis for unique coordinates at (3,4). The
[real-line](../../examples/algebra/dimension_extension/scalar/main.lit) and
[zero-space](../../examples/algebra/dimension_extension/zero/main.lit) consumers
compute 1 and 0 and extend empty prefixes. All fields are supplied; no scalar
ordering is used.

Run python3 examples/algebra/dimension_extension/check.py for strict sources,
ten generic theorem calls and two construction carriers, sixteen final-only
controls, installed imports and std/WiX equality. The controls cover missing
domains/hypotheses, wrong sizes/values, invalid append indices and a concretely
changed prefix. These additions introduce no native rule, source trust or
overload. The linear_dimension export below proves general rank-nullity. Further
subspace dimension results and the remaining undergraduate lanes need their own proofs.


## Inherited subspaces and finite dimension

The subspace export turns an existing subset U with
$vector_space::is_subspace(K,F,V,X,U) into a VectorSpace using exactly X's
operations restricted to U. K/F/V/X retain their existing supplied-field
contracts, U is in power_set(V), and zero-dimensional subspaces are admitted.
No new scalar operations, choice of basis, native rule or trust is introduced.

| Construction | Fixed contract |
| --- | --- |
| \subspace::restricted_add<K,F,V,X,U>(u,v) | u,v in U; returns X.add(u,v) in U; requires the subspace proof |
| \subspace::restricted_smul<K,F,V,X,U>(a,v) | a in K, v in U; returns X.smul(a,v) in U; requires the subspace proof |
| \subspace::restricted_space<K,F,V,X,U> | The tuple (X.zero, restricted_add, restricted_smul), a VectorSpace over carrier U; requires the subspace proof |
| \subspace::inclusion<V,U>(u) | u in U, U in power_set(V); the same vector u viewed in V, also when U is empty |

Use subspace_is_nonempty before writing U in a VectorSpace carrier, then
restricted_space_is_vector_space before binding the constructed structure.
Named exported theorems supply these facts across module boundaries; importing
a module does not merge all its anonymous ambient facts.

| Theorem | Result and additional premises |
| --- | --- |
| subspace_is_nonempty(K,F,V,X,U) | A subspace is nonempty |
| subspace_inverse_exists(K,F,V,X,U,x) | x in U has y in U with X.add(x,y)=X.zero |
| sequence_in_ambient(V,U,n,v) | v in finite_seq(U,n) also belongs to finite_seq(V,n); subset U suffices |
| restricted_space_is_vector_space(K,F,V,X,U) | The guarded constructed value has its declared VectorSpace carrier |
| inclusion_is_linear(K,F,V,X,U) | The inclusion from the inherited space to X is linear |
| subspace_combination_equals_ambient(K,F,V,X,U,n,c,v) | The same coefficient/vector lists have the same selected linear-combination value in U and V |
| subspace_independent_is_ambient_independent(K,F,V,X,U,n,v) | Independence in the inherited space implies ambient independence |
| ambient_independent_is_subspace_independent(K,F,V,X,U,n,v) | Ambient independence implies inherited independence |
| subspace_span_equals_ambient(K,F,V,X,U,n,v) | Both carriers give exactly the same span of v in finite_seq(U,n) |
| finite_dimensional_subspace_is_finite_dimensional(K,F,V,X,U) | Ambient finite-dimensional evidence gives inherited finite-dimensional evidence |
| subspace_dimension_le_ambient(K,F,V,X,U) | Inherited dimension is at most ambient dimension; both finite-dimensional facts are explicit value domains |
| ambient_is_subspace(K,F,V,X) | The whole carrier V is a subspace |
| zero_is_subspace(K,F,V,X) | {X.zero} is a subspace |

Except for sequence_in_ambient and the last two constructors of subspace facts,
these theorems take a proved subspace. Combination/independence/span interfaces
use natural n, coefficients in finite_seq(K,n) when present, and vectors in
finite_seq(U,n). No order on the scalar field is assumed. The finite maximum in
the proof is over natural list lengths, not over field elements.

This complete imported consumer first establishes the carrier facts, then uses
the finite-dimensional theorem and the guarded dimension bound. It assumes the
same std import setup as the other examples:

```litex
claim:
    ? forall K nonempty_set,field &Algebra::field::Field<K>,V nonempty_set,space &Algebra::vector_space::VectorSpace<K,field,V>,U power_set(V):
        $Algebra::vector_space::is_subspace(K,field,V,space,U)
        =>:
            $is_nonempty_set(U)
    by thm Algebra::subspace::subspace_is_nonempty(K,field,V,space,U) => $is_nonempty_set(U)

claim:
    ? forall K nonempty_set,field &Algebra::field::Field<K>,V nonempty_set,space &Algebra::vector_space::VectorSpace<K,field,V>,U power_set(V):
        $Algebra::vector_space::is_subspace(K,field,V,space,U)
        =>:
            \Algebra::subspace::restricted_space<K,field,V,space,U> $in &Algebra::vector_space::VectorSpace<K,field,U>
    by thm Algebra::subspace::restricted_space_is_vector_space(K,field,V,space,U) => \Algebra::subspace::restricted_space<K,field,V,space,U> $in &Algebra::vector_space::VectorSpace<K,field,U>

thm finite_subspace:
    ? forall K nonempty_set,field &Algebra::field::Field<K>,V nonempty_set,space &Algebra::vector_space::VectorSpace<K,field,V>,U power_set(V):
        $Algebra::vector_space::is_subspace(K,field,V,space,U)
        $Algebra::basis::is_finite_dimensional(K,field,V,space)
        =>:
            $Algebra::basis::is_finite_dimensional(K,field,U,\Algebra::subspace::restricted_space<K,field,V,space,U>)
    by thm Algebra::subspace::finite_dimensional_subspace_is_finite_dimensional(K,field,V,space,U) => $Algebra::basis::is_finite_dimensional(K,field,U,\Algebra::subspace::restricted_space<K,field,V,space,U>)

thm finite_subspace_bound:
    ? forall K nonempty_set,field &Algebra::field::Field<K>,V nonempty_set,space &Algebra::vector_space::VectorSpace<K,field,V>,U power_set(V):
        $Algebra::vector_space::is_subspace(K,field,V,space,U)
        $Algebra::basis::is_finite_dimensional(K,field,V,space)
        $Algebra::basis::is_finite_dimensional(K,field,U,\Algebra::subspace::restricted_space<K,field,V,space,U>)
        =>:
            \Algebra::dimension::finite_dimension<K,field,U>(\Algebra::subspace::restricted_space<K,field,V,space,U>)<=\Algebra::dimension::finite_dimension<K,field,V>(space)
    by thm Algebra::subspace::subspace_dimension_le_ambient(K,field,V,space,U) => \Algebra::dimension::finite_dimension<K,field,U>(\Algebra::subspace::restricted_space<K,field,V,space,U>)<=\Algebra::dimension::finite_dimension<K,field,V>(space)

```

The [subspace consumer](../../examples/algebra/subspaces/main.lit) uses the
existing real-plane model. The x-axis has inherited dimension 1, the full plane
has inherited dimension 2, and {zero} has inherited dimension 0. It verifies
T(x,y)=(x,0), e2 in its kernel, e1 in its image, then obtains finite-dimensional
kernel/image structures and dimension bounds of 2. The rank_nullity consumer below reuses that fixture to compute both
projection dimensions as 1 and applies the general rank-nullity theorem.

Keep canonical template arguments when using span results. In the checked
consumer, an alias for the constructed space works as a typed structure and as
the ordinary argument to finite_dimension. An attempted span equality obtained
solely by replacing that template argument with an equal alias was rejected by
the tested verifier. The maintained proofs use the canonical constructed space;
no changed mathematical definition or trust compensates for that boundary.

Run python3 examples/algebra/subspaces/check.py for the imported consumer,
source, generic contracts, thirteen last-statement controls, real installed
archive/shared-data discovery, and source/WiX payload equality. Pass --binary
/path/to/litex to select a particular release executable. These focused checks
are independent of any claim about compiling the current Rust checkout.


## Linear-map rank, nullity and finite decomposition

The finite_decomposition and linear_dimension exports use the existing supplied
Field and VectorSpace contracts. The source and target share the field, but the
rank-nullity theorem does not assume the target is finite-dimensional. Natural
list lengths include zero. No basis is selected as a public canonical basis.

| Source value | Exact mathematical domain and result |
| --- | --- |
| \finite_decomposition::concatenate_lists<S,m,n,left,right> | S nonempty, m,n in N, left/right in finite_seq(S,m/n); a list in finite_seq(S,m+n). At j in 1..m+n it is left(j) when j<=m and right(j-m) otherwise. |
| \linear_dimension::linear_map_rank<K,F,V,X,W,Y>(T) | T linear from X on V to Y on W, with finite-dimensional inherited image; returns its natural dimension. Source finiteness is sufficient, not part of the value's exact guard. |
| \linear_dimension::linear_map_nullity<K,F,V,X,W,Y>(T) | T linear, with finite-dimensional inherited kernel preimage(T,Y.zero); returns its natural dimension. |

Each name has one fixed parameter contract. Rank and nullity have six template
parameters and one ordinary function argument. Concatenation has five template
parameters; ordinary list application has one legal index. There is no arity
or scalar/vector dispatch.

The four finite_decomposition theorems are concatenate_lists_carrier,
prefix_has_concatenation_decomposition, list_splits_at_length and
concatenated_linear_combination. They respectively expose the list type, split
a supplied prefix, split any list at a natural length, and express the combined
linear combination as the sum of its two parts. Prefix decomposition requires
is_prefix_of_length; arbitrary splitting returns both lists existentially.

The seventeen linear_dimension theorems have these roles:

| Names | Contract |
| --- | --- |
| function_range_carrier, function_range_is_nonempty | Any total map between nonempty sets has a nonempty range contained in its codomain. |
| linear_kernel_is_nonempty | Linearity supplies the zero preimage witness. |
| linear_kernel_space_carrier, linear_image_space_carrier | The inherited kernel/image tuples have their VectorSpace carriers after linearity. |
| mapped_list_in_range | Mapping a finite source list gives a list in the actual range; no linearity is needed. |
| spanning_list_maps_onto_image | A source spanning list maps to an inherited image spanning list under linearity. |
| finite_source_has_finite_image, finite_source_has_finite_kernel | Source finite dimension and linearity imply the two inherited finite-dimensional facts. |
| kernel_prefix_tail_spans_image | If prefix++tail spans the source and the prefix is killed by T, the mapped tail spans the image. |
| kernel_in_prefix_span_makes_tail_image_independent | If prefix++tail is independent and the prefix span contains the kernel, the mapped tail is independent in the target. |
| finite_source_rank_carrier, finite_source_nullity_carrier | Source finite dimension and linearity give the selected value in N, R and C, allowing typed arithmetic at theorem boundaries. |
| rank_nullity | Source finite dimension and linearity give rank(T)+nullity(T)=finite_dimension(X), with arbitrary target. |
| finite_target_has_finite_image | Target finite dimension and linearity are another sufficient condition for finite image; they do not imply finite kernel. |
| rank_le_source_dimension, nullity_le_source_dimension | Each value is at most source dimension. Besides source finiteness and linearity, the corresponding image/kernel finiteness is an explicit value domain in these inequality interfaces. |

All seven-parameter map theorems use (K,F,V,X,W,Y,T), followed by natural list
lengths and the supplied lists where applicable. See the complete exact
headers in the source and the independently checked imported
[contracts](../../examples/algebra/rank_nullity/contracts.lit). Those contracts
also check the value definitions using only image/kernel finiteness, and rank
availability from target finiteness without source finiteness.

The proof of rank-nullity takes a finite kernel basis, views it in the source,
extends it while retaining its ordered prefix, and splits off a tail. The tail
images form an image basis. Their length plus the kernel basis length is the
source basis length, and basis-length invariance turns that equality into the
selected dimension formula. Empty prefixes and tails need no separate axiom.

Imported callers must establish constructor facts in their own context before
using guarded values: range subset/nonemptiness, kernel/image subspace facts,
the inherited VectorSpace carriers, then the required finite-dimensional facts.
The two numeric carrier theorems make rank/nullity arithmetic available. A
module import does not merge its anonymous ambient facts.

Here is a complete small consumer with the std import alias Algebra:

```litex
have fn left(j closed_range(1,1)) R=3

have fn right(j closed_range(1,1)) R=5

\Algebra::finite_decomposition::concatenate_lists<R,1,1,left,right>(1)=left(1)=3

\Algebra::finite_decomposition::concatenate_lists<R,1,1,left,right>(2)=right(2-1)=right(1)=5
```

The [real-plane consumer](../../examples/algebra/rank_nullity/main.lit) reuses
the existing plane and projection fixture. It computes projection rank/nullity
(1,1), zero-map (0,2), and identity (2,0). The
[empty-list consumer](../../examples/algebra/rank_nullity/empty_lists.lit) checks
both empty pieces, the entirely empty concatenation, legal boundary entries,
and all three empty-piece splitting cases.

Run python3 examples/algebra/rank_nullity/check.py --binary /path/to/litex.
It checks strict sources and callers, all new named contracts, twenty isolated
last-statement rejection controls, real archive/shared-data std discovery, and
source/WiX payload equality. These source proofs add no native rule, BT, public
prop, trust, parser change or operation overload. Infinite/cardinal dimensions,
representation matrices, further linear-operator and spectral theory remain
separate work.


## Linear-map criteria and inverse bijections

The linear_criteria export connects native injective, surjective and bijective
properties with the previously selected finite dimensions. It introduces no
parallel isomorphism predicate: a linear isomorphism is a supplied linear map
that is bijective on its stated source and target.

Its one new source value is \linear_criteria::inverse_bijection<V,W,T>(y).
V and W are sets, possibly empty, T has type fn(v V) W and must be proved
bijective; y is in W and the result is the unique x in V with T(x)=y. The
three template parameters and one ordinary argument have one fixed contract.
The inverse selector itself requires neither linearity nor finite dimension.
Its linearity theorem adds the actual linear-map premise over the same supplied
field, with no finite-dimensional assumption on either space.

| Theorems | Contract |
| --- | --- |
| empty_span_is_zero | Any empty vector list has span {zero}. |
| zero_dimension_is_zero_space, zero_space_has_zero_dimension | Under the finite-dimension value domain, dimension zero is equivalent to carrier {zero}. |
| equal_dimension_subspace_is_ambient | A finite-dimensional inherited subspace with ambient dimension equals the whole ambient carrier; both value domains and subspace evidence are explicit. |
| whole_subspace_dimension_equals_ambient | If that subspace carrier is the whole ambient carrier, the two selected dimensions agree. |
| inverse_bijection_right_identity, inverse_bijection_left_identity | T(inv(y))=y and inv(T(x))=x for any bijection between sets. |
| inverse_bijection_is_bijective, inverse_bijection_is_linear | The inverse is bijective; a linear bijection has a linear inverse, without dimension assumptions. |
| zero_nullity_is_injective, injective_has_zero_nullity | For a linear map with finite kernel, nullity zero is equivalent to injectivity; source finiteness is not required. |
| full_source_rank_is_injective, injective_has_full_source_rank | With finite source and linearity, rank=source dimension is equivalent to injectivity. |
| surjective_has_full_range, full_range_is_surjective | Surjectivity is equivalent to range=codomain, including empty sets; no linearity or dimension assumptions. |
| surjective_has_full_target_rank, full_target_rank_is_surjective | With finite target and linearity, rank=target dimension is equivalent to surjectivity; source finiteness is not required. |
| injective_dimension_bound, surjective_dimension_bound | For two finite-dimensional spaces, injectivity gives dim(source)<=dim(target), surjectivity the reverse bound. |
| equal_dimension_injective_is_bijective, equal_dimension_surjective_is_bijective | For a supplied linear map between finite-dimensional spaces of equal dimension, either property gives bijectivity. |
| bijective_preserves_dimension | A supplied linear bijection between finite-dimensional spaces preserves selected dimension. |

Map theorems use (K,F,V,X,W,Y,T). Zero-space and subspace helpers use
(K,F,V,X) and, when present, U power_set(V). empty_span_is_zero also takes a
list in finite_seq(V,0). Inverse identity/bijectivity theorems use (V,W,T),
followed by y in W or x in V for the respective identity. All exact headers
and 22 imported named calls are in the source and consumer contracts.

The proofs use empty basis spans, inherited/ambient basis comparison and
rank-nullity. Pointwise constructor/finite-image facts are materialized where
guarded definition unfolding or conclusion storage needs them. No stronger
mathematical premise is added to the main criteria.

This complete standalone consumer checks the empty bijection and its inverse:

```litex
have fn empty_map(x {}) {}=x

by def $injective({},{},empty_map)

claim:
    ? forall y {}:
        exist x {} st {y=empty_map(x)}
    witness exist x {} st {y=empty_map(x)} from y

by def $surjective({},{},empty_map)

by def $bijective({},{},empty_map)

\Algebra::linear_criteria::inverse_bijection<{},{},empty_map> $in fn(y {}) {}

by thm Algebra::linear_criteria::inverse_bijection_is_bijective({},{},empty_map) => $bijective({},{},\Algebra::linear_criteria::inverse_bijection<{},{},empty_map>)

by thm Algebra::linear_criteria::surjective_has_full_range({},{},empty_map) => fn_range(empty_map)={}

by thm Algebra::linear_criteria::full_range_is_surjective({},{},empty_map) => $surjective({},{},empty_map)
```

The [coordinate-exchange consumer](../../examples/algebra/linear_criteria/main.lit)
proves that (x,y)->(y,x) is bijective using the equal-dimension injectivity
criterion, obtains its linear inverse and checks inv((3,4))=(4,3), rank 2 and
nullity 0. Its coordinate calculations first expose the actual callable
structure fields. The
[boundary consumer](../../examples/algebra/linear_criteria/boundaries/main.lit)
checks dimension zero, identity on the zero space, and the empty-set bijection.
The README code is also the isolated
[inverse-set consumer](../../examples/algebra/linear_criteria/inverse_sets/main.lit).

Run python3 examples/algebra/linear_criteria/check.py --binary /path/to/litex
for strict source/caller/contracts, twenty isolated last-statement controls,
actual installed std discovery and std/WiX equality. A rejected control records
a missing proof obligation or a wrong concrete result, not a proof of the
logical negation of every rejected formula.

These are checked source derivations, with no trust, new public prop, native
Obj/Fact, BT, rule, strategy, AST/runtime or compiler change. Existence of a
linear isomorphism from dimension equality alone, direct sums, representation
matrices, canonical complements and further operator theory remain separate
work. This export does not close the linear-algebra curriculum.


## Coordinates, prescribed basis images and isomorphism existence

The coordinate_maps export constructs a linear map by specifying the images
of an ordered source basis. The target image list is arbitrary: repeated,
dependent or zero images remain legal. The target need not be finite-dimensional.

| Source value | Fixed contract |
| --- | --- |
| \coordinate_maps::unit_coefficients<K,F,n,j>(k) | Four template parameters: K nonempty, F a supplied Field, n in N, j in closed_range(1,n). The value is in finite_seq(K,n); its one ordinary index k is also in closed_range(1,n), returning F.one at j and F.zero elsewhere. There is no valid j when n=0. |
| \coordinate_maps::linear_map_from_basis<K,F,V,X,W,Y,n,u,w>(x) | Nine template parameters, one ordinary x in V. X/Y are VectorSpaces over the same supplied K/F, n in N, u in finite_seq(V,n) is a proved basis, and w in finite_seq(W,n) is arbitrary. The result is the target combination of w with the source coordinates of x. |

Whole function values and their one-argument evaluation share these fixed
contracts. Neither name uses arity/type dispatch. The map constructor requires
no target-basis evidence; that evidence is added only to the inverse theorems.
There is no chosen canonical basis or canonical isomorphism of two spaces.

| Theorems | Mathematical role |
| --- | --- |
| basis_coordinates_reconstruct | Combining the selected coordinates in their basis returns the input vector. |
| basis_coordinates_add, basis_coordinates_smul | Coordinates commute with vector addition and scalar multiplication via the existing coefficient-list operations. |
| unit_coefficients_carrier, unit_linear_combination | The unit coefficient value has length n and its combination selects the jth vector. |
| basis_coordinates_of_entry | A basis vector has its corresponding unit coefficient list. |
| linear_map_from_basis_carrier, linear_map_from_basis_is_linear | The chosen value is a complete V->W function and is linear. |
| linear_map_from_basis_entry | The jth basis vector maps to the jth supplied image. |
| linear_map_from_basis_on_combination | Any source combination with coefficients c maps to the target combination with the same c. |
| linear_map_agreeing_on_basis_is_extension | A supplied linear T taking u to w equals the constructed map. |
| linear_maps_equal_on_basis | Two supplied linear maps agreeing on the source basis are equal as functions. |
| basis_maps_round_trip, basis_maps_are_bijective | If w is also a basis, the reversed construction is a left inverse and the forward construction is bijective. The other round trip follows by swapping the spaces/lists. |
| basis_map_inverse | The existing inverse_bijection of that map equals the reversed construction, assuming both basis facts. |
| linear_bijection_maps_basis_to_basis | Any supplied linear bijection sends a basis to a basis, without extra finite-dimensional assumptions. |
| equal_finite_dimensions_have_linear_bijection | Finite-dimensional X/Y of equal selected dimension admit some T:V->W that is linear and bijective. No candidate T or bases are supplied as premises. |

These are seventeen named source theorems. Map construction interfaces use
(K,F,V,X,W,Y,n,u,w), followed by x, c, j or a supplied T as indicated. Coordinate
helpers use (K,F,V,X,n,u), followed by vectors/scalars/indices. The map-equality
interface uses (K,F,V,X,W,Y,n,u,T,S); the basis-image interface uses
(K,F,V,X,W,Y,n,u,T). Existence takes only (K,F,V,X,W,Y). Exact headers and all
imported calls are in the source and consumer contracts.

The existence proof obtains a basis of source dimension in each space, then
returns their constructed basis map with its linearity and bijectivity proofs.
Together with linear_criteria::bijective_preserves_dimension this classifies
finite-dimensional spaces over the same supplied field up to linear
isomorphism by dimension. It does not select one isomorphism independently of
bases. Here is the complete standalone imported consumer:

```litex
thm finite_dimensional_isomorphism_exists:
    ? forall K nonempty_set,field &Algebra::field::Field<K>,V nonempty_set,source &Algebra::vector_space::VectorSpace<K,field,V>,W nonempty_set,target &Algebra::vector_space::VectorSpace<K,field,W>:
        $Algebra::basis::is_finite_dimensional(K,field,V,source)
        $Algebra::basis::is_finite_dimensional(K,field,W,target)
        \Algebra::dimension::finite_dimension<K,field,V>(source)=\Algebra::dimension::finite_dimension<K,field,W>(target)
        =>:
            exist T fn(v V) W st {$Algebra::vector_space::is_linear_map(K,field,V,source,W,target,T),$bijective(V,W,T)}
    release thm Algebra::coordinate_maps::equal_finite_dimensions_have_linear_bijection(K,field,V,source,W,target)
```

The [plane consumer](../../examples/algebra/coordinate_maps/main.lit) maps both
standard basis vectors to e1, checks (3,4)->(7,0) and proves noninjectivity. A
second target basis comes from the existing coordinate swap. Its constructed
map sends (3,4)->(4,3), its inverse sends (4,3)->(3,4), and the inverse agrees
with the reversed basis map. The existing swap fixture appends only a named
export of two previously checked facts.

The [zero-dimensional consumer](../../examples/algebra/coordinate_maps/boundaries/main.lit)
uses the inherited zero subspace over the same real field. An empty image list
constructs the linear map into the whole plane, and that map is not surjective.
Two empty bases give a zero-space isomorphism. Equal-dimension existence works
at dimension0, while a linear bijection from dimension0 to dimension2 is
explicitly ruled out.

Run python3 examples/algebra/coordinate_maps/check.py --binary /path/to/litex
for strict sources/callers, seventeen generic named contracts, twenty
last-statement controls, actual installed std discovery and std/WiX equality.
The controls test the exact missing obligations or wrong concrete conclusions;
rejection alone is not a theorem of logical negation.

No new public/proof-local prop, native Obj/Fact, BT, rule, strategy, parser,
AST/runtime, overload or compiler change is introduced. One narrow draft trust
in the selected-inverse identification is discharged by explicitly using
injectivity; the maintained source is strict and trust-free. Direct sums,
representation matrices and further operator/spectral theory remain open.
