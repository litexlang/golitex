# Algebraic interfaces

The group export develops groups, subgroups and homomorphisms. Its source is
`group.lit`. The exports `field` and `vector_space` retain the existing
scalar-field and vector-space interfaces and their foundational linear-map
theory. This package owns the shared declarations used by the lectures and
independent consumers.

## Operations and laws

`Group<A nonempty_set>` packages multiplication, an identity and inversion,
together with associativity and both identity/inverse laws. Nonemptiness is
part of the carrier because a group supplies an identity. The trivial group
is permitted. Commutativity is the separate relation `is_abelian(A,G)`.
A parallel predicate certifying the same group laws would add no independent
mathematical role.

Identity uniqueness, inverse uniqueness, cancellation and unique solutions of
`G.mul(a,x)=b` are proved consequences of the structure laws. They must not be
added as assumptions or fields merely to simplify a consumer's proof.

## Subgroups and maps

`is_subgroup(A,G,S)` keeps the ambient operations and requires the identity,
multiplicative closure and inverse closure in `S power_set(A)`.
`is_normal_subgroup` adds conjugation closure. A separately supplied group on
the same subset could have unrelated operations and is not a substitute.

`is_homomorphism(A,G,B,H,f)` is a relation on an ordinary complete map
`f fn(x A) B`. It requires only multiplication preservation. Identity and
inverse preservation follow from group cancellation; assuming them would
obscure those results.

## Kernels and injectivity

`\kernel<A,B,H,f>` is the subset `{x A: f(x)=H.one}`. The template parameters
determine its carrier; the domain group's operations are not needed just to
form that set. The kernel exists even for a map not known to be a homomorphism,
while its subgroup/normality theorem requires the homomorphism premise.

`has_trivial_kernel(A,G,B,H,f)` states that every element mapping to `H.one`
equals `G.one`. For homomorphisms it is equivalent to native
`injective(A,B,f)`. A general map with that preimage condition alone need not
be injective, so the homomorphism premise remains explicit.

## Dependency order and uses

Group laws give cancellation and inverse uniqueness. Those results give
identity/inverse preservation by homomorphisms. The kernel construction and
preservation results give kernel normality; cancellation then gives the two
directions of the injectivity criterion. Subgroup intersection is independent
of the kernel construction.

The map/closure extension adds whole-carrier and singleton-identity subgroups,
normal intersections, homomorphism ranges, subgroup/normal inverse images,
identity maps and composition. Native fn_range(f), preimage_set(f,S) and
compose(g,f) remain the actual constructions. The proof runs from established
identity/inverse preservation to image and inverse-image closure; normality
uses preservation of the conjugating product. Composition preserves
multiplication by applying the two supplied homomorphism laws in order.
No commutativity, injectivity or surjectivity is needed. An arbitrary target
image need not be normal, so only subgroup membership is exported for ranges.

This source checkpoint has27 top-level statements/20 thms with the same Group
structure, five props and one kernel template. It adds no native rule, search
permission, trust or compiler contract. Eight imported generic signatures and
43 actual integer/trivial statements have passed. All24 fresh focused checks
pass, including model30, noncommutative15, README1, legacy group34/lecture31,
14 final-only refusals, both installed layouts and std/WiX80-file/reference
agreement. Five named instance theorems publish the existing Heisenberg model
facts and projection formula for its new consumer. No original model
mathematics is changed. Receipt: std-group-map-laws-acceptance-2026-10-28.json.


Integer addition, multiplication-by-two and the zero map supply applications.
The trivial group checks the permitted degenerate case. A real Heisenberg
group supplies a noncommutative consumer without changing the general laws.
These are concrete instances, not additional std declarations.

## Scalar fields and vector spaces

`field::Field<K nonempty_set>` packages zero, one, addition, negation,
multiplication and inversion with the existing field laws. Zero differs from
one, and inversion has the exact domain `x K: x != zero`. A total inverse
with an arbitrary zero value would change the interface's mathematical meaning.
This export does not introduce a ring-to-field coercion hierarchy.

`vector_space::VectorSpace<K,field,V>` packages vector zero, addition and
scalar multiplication over that supplied field. Its addition laws include
existence of additive inverses; uniqueness is derived. It permits the
zero-dimensional, one-element space. The data and laws stay in one struct,
without a parallel law-certificate predicate.

`is_subspace` is a relation on an existing subset using ambient operations.
`is_linear_map` is a relation on a complete supplied function between two
spaces over the same field. Additivity and homogeneity are both required.
Preservation of zero, closure under composition, and the kernel/range subspace
theorems are consequences, not extra definition clauses.

The identity, constant-value and composition templates construct ordinary
functions. The zero-map theorem requires the actual target zero. Kernel and
image use the existing `preimage(T,target.zero)` and `fn_range(T)` values;
there is no additional kernel or image selector. For linear maps, a zero kernel
is equivalent to injectivity without finite-dimensional assumptions.

Dependencies run from Field to VectorSpace, then the subspace/linearity
relations and basic zero identities, then identity/zero/composition maps,
kernel/image and injectivity. Scalar arithmetic, native sets and functions
are reused independently of the group export. Finite spans consume these
foundations through finite_span. Shared independence, conditional coordinates,
dependence, span reduction and finite basis existence are supplied by the
later exports. Basis-length invariance, finite dimension selection and
rank-nullity are provided by the subsequent exports.

The exports use native sets, maps, struct laws and equality checking, with
ordinary source proofs. No quotient construction, Lagrange theorem, ring
hierarchy, general dimension selector or new native mathematical schema is
part of these slices.


## Finite combinations and span

The finite_span export preserves the lecture's ordered-list model. Coefficients
and vectors have exact carriers finite_seq(K,n) and finite_seq(V,n), indexed
from 1 to n. A partial-sum trace has domain closed_range(0,n), begins at vector
zero and adds one coefficient-scaled vector at every positive step. Repeated
vectors and empty lists are valid; this is not a finite-set representation.

The relation has_linear_combination_value supplies a trace ending at a candidate
value. is_linear_combination allows coefficients to vary. Existence follows
from induction, uniqueness from comparing traces by induction, and only then
is linear_combination selected by exist!. These separate roles avoid defining
an unrestricted value before its mathematical justification.

Span is the subset of V consisting of all such combinations; spans asserts
that this subset is V. Zero/add/neg/smul coefficient lists have exact length n.
Entry and trace lemmas establish zero/add/smul identities for the selected value,
which then prove zero containment and addition/scalar closure of span. map_vectors
transports an ordered list through a complete function; preservation of its
combination additionally requires a linear map over the same scalar field.

Dependencies: Field/VectorSpace -> partial/value/combination relations -> span;
trace existence+uniqueness -> selected combination; coefficient constructions
and trace algebra -> selected-value algebra -> span subspace; linearity and
trace transport -> linear-map preservation. No independence, basis, dimension
or general exchange theorem is introduced by this extraction. The real-plane lecture is the source of the promoted interfaces. Two checked
source theorems publish the zero coefficient list's carrier and the selected
combination's defining relation, because imported names do not merge local
generated definition facts. Independent scalar, empty-list and singleton
consumers check these interfaces. No new native representation is introduced.


The dependency edges are explicit: Field/VectorSpace --signature--> trace and
candidate relations; partial-sum recurrence --definition--> candidate value;
trace induction --existence/uniqueness--> selected combination;
coefficient constructions and trace lemmas --proof--> selected-value algebra;
selected-value algebra --proof--> span closure; linearity and trace transport
--proof--> map preservation. The import-facing carrier/property theorems publish
already checked definition consequences. This graph is acyclic; the span set
can be defined before selection because it depends only on the candidate
relation. Independence and basis results consume it later.


## Independence, bases and coordinates

A finite ordered list is independent when every zero-valued combination has
only zero coefficients. A basis adds spanning. Neither notion requires a
chosen dimension, and an empty basis is legitimate for the zero space.
The shared basis export preserves those relations and the existing
prefix/deletion and length-two dependence interfaces.

General coordinate uniqueness follows forward from coefficient algebra:
construct the negative of the right coefficient list, show right+negative is
zero, use equality of the two combination values to show left+negative also
has zero value, apply independence, then cancel each scalar coefficient.
Spanning separately supplies a representation for every vector. Existence and
uniqueness together justify the guarded basis_coordinates function. The
operation keeps one fixed contract over a supplied scalar field and exact
basis list; it is not overloaded by arity or scalar/vector type.

The new interface is conditional on an actual basis, not merely a spanning
list or a supplied length. The general proofs apply to arbitrary finite n,
including n=0. Finite basis existence is supplied separately by basis_existence
below. The later basis_comparison export proves equal lengths of finite bases;
no general dimension selector is supplied. These interfaces are checked by
independent real-line and empty-basis uses,
generic theorem-contract consumers and executable missing-premise/value/domain
controls. No general dimension selector is inferred from a chosen basis length.


## General finite dependence

For a nonzero coefficient list, the support is the subset of integer indices
where its entry differs from scalar zero. This subset of 1..n is finite and
nonempty, so its greatest index exists. Ordering is used only on indices;
no order is imposed on the supplied field.

A restricted trace is a partial-sum trace for restricted coefficients and
vectors. A zero coefficient tail leaves the final sum equal to the sum at the
last nonzero index. At that index, the zero-sum relation can be solved using
the nonzero scalar inverse, vector-space laws and additive-inverse uniqueness.
Scaling the earlier coefficients then represents the selected vector in the
span of its preceding prefix. The empty-list independence fact handles n=0.

These checked source steps prove the general dependence lemma in `dependence.lit`. They
are not a dimension selector or a basis-exchange proof by themselves. Existing
native finite-set bounds, subset finiteness and induction are reused; no new
native schema or field ordering is proposed. The prefix helper accepts a supplied trace on 0..m with pointwise equality to
the original trace. It proves the restricted relation for that same function;
it does not introduce a second selector or impose an order on field elements.
The exact imported contracts, length-three example, empty/singleton cases and
negative boundaries are maintained in examples/algebra/dependence.


## General span reduction

Subspaces contain zero and are closed under addition and scalar multiplication,
so induction on a partial-sum trace places any finite combination of their
members in the subspace. A coefficient list with one scalar one and all other
entries zero places each generator in its own span. Together these facts make
the finite span the least subspace containing the listed vectors.

This gives a forward route to transport: if all generators of one list belong
to another list's span, its whole span is included there. Deleting index k
preserves span whenever the deleted vector already belongs to the remaining
list's span. The removed-list relation supplies generator matching on either
side of k; no coefficient redistribution representation is needed.

For a dependent nonempty list, the checked dependence lemma supplies a vector
in the span of its preceding prefix. That prefix is included among the
remaining list's generators, so the same removal criterion applies. This
checked result shortens the list by one. The following basis_existence export
uses it for extraction. The later exchange and basis_comparison exports
supply single-step exchange, length comparison and invariant finite basis length.


## Finite basis existence

A basis extracted from a finite spanning list keeps both a length bound
and provenance of its vectors. The checked existential returns m<=n, a basis
list of length m, and fn_range(basis) subset fn_range(vectors). Range inclusion
certifies that its values are among the supplied generators; it does not claim
a selected ordering or a unique basis.

Removing an index preserves inclusion of list ranges. Induction on the finite
length then quantifies over every spanning list of that length: an independent
list already forms a basis, and a dependent positive-length list reduces to a
shorter spanning list with its range included in the original. The empty list
uses the existing empty-list independence theorem. A local atomic proposition
holds this quantified mathematical invariant for the induction interface.

Finite dimensionality supplies one finite spanning list, so the extraction
result implies finite basis existence. Neither existence nor the length bound
proves that all bases have the same length; no chosen basis or dimension
operation is supplied.


## Single-step exchange

A list update relation compares a supplied original list, a legal index, a
new value and a supplied replacement list. Its witness is constructed locally
by cases; no default selected list operation is needed by the exchange proof.

Weighted contributions, rather than whole generators, are the exact data
needed for subspace closure of a finite combination. Ordinary generator
closure follows from that principle. A one-supported coefficient list has
combination value equal to its supported scalar-vector contribution; this
also subsumes the generator-in-own-span delta proof.

If a represented vector replaces generator k with a nonzero coefficient,
the remaining generator contributions and the represented vector lie in the
new span. Subspace additive/scalar cancellation then puts the old k-th vector
there as well, giving one inclusion. The reverse inclusion uses that every
new generator already lay in the old span. This single-step exchange is a
prerequisite for the longer independent-versus-spanning comparison; it does
not itself certify equal lengths of all bases.

The exchange proof splits coefficients into the selected contribution and the
remaining contributions. Sparse evaluation and coefficient addition identify
their sum with the supplied value. Weighted subspace closure puts the remaining
value in the new span; additive and nonzero-scalar cancellation recover the
old generator. A combination outside a subspace must have a nonzero term outside
it. Applying this to the empty span supplies the existential replacement for
a nonzero member. Empty lists have no legal update index; a zero represented
value is still allowed by the explicit nonzero-coefficient criterion.


## Independent/spanning comparison and invariant finite basis length

A vector in the span of its preceding prefix would create a zero combination
of the entire list whose next coefficient is minus one. Independence rules
this out. In the exchange induction, the embedded prefix occupies distinct
positions. A new independent vector is outside its prefix span; a nonzero term
outside that subspace therefore occurs at an unoccupied position. Replacing
that generator preserves the span and extends the injective position map.

The final finite injection gives the length inequality, including the empty
case. Two bases give inequalities in both directions, hence equal lengths.
The already checked finite basis-existence theorem then supplies a unique
natural basis length for every finite-dimensional supplied space. The zero
space is included with length zero. Two local props encode the embedding and
its conditional existence during induction. No public witness package or
selected dimension operation is added by the comparison export itself.
The following dimension export supplies that separately justified value.


## Ordered extension and guarded finite dimension

Appending a vector outside a list span preserves independence: restrict a
zero combination to the old prefix, inspect its last coefficient, and either
apply old independence or solve the zero sum to contradict the outside-span
condition. No scalar order or inversion at zero is used. At a known basis
length, another outside vector would make an independent list too long.

Induction on the remaining natural length preserves every existing entry.
A spanning current list is already a basis; otherwise append an outside
vector, extend it at one smaller deficit, and compose the two prefix relations.
The dual maximal-length spanning criterion follows by removing one redundant
vector and contradicting the length bound. Empty lists and the zero space are
included. One local prop holds the guarded deficit invariant.

The unique natural basis length now supports the source-selected function
finite_dimension, with K/F/V closed as template parameters and space X as its
single argument. Its finite-dimensional domain is proved before use, not
guessed by the selector. All dimension value theorem settings retain that
domain explicitly. Existing basis/spanning proofs supply it separately.
Independent/spanning dimension bounds and equal-size basis criteria then
follow from the comparison and extension interfaces.

The primary plane consumer exercises actual nonempty prefix growth, with
dimension 2 and preserved first entry e1. Real/zero spaces test dimensions
1/0 and empty prefixes. There is no selected canonical basis or native rule.


## Inherited subspaces and bounded finite dimension

A subspace is first a subset using ambient operations. Restrict those operations
without changing vector values: restricted_add and restricted_smul return U,
and the inherited struct is their tuple with the ambient zero. An ambient
additive inverse belongs to U by subspace additive cancellation. The joint
identity/inverse clause matches the VectorSpace struct contract. Nonemptiness,
the struct carrier and finite-sequence inclusion have named exported proofs so
an imported consumer can establish each later carrier before using it.

The inclusion is linear. Map a finite combination through it and identify the
mapped vector list with the original list. Selected combination values agree;
uniqueness transfers a zero combination and hence independence in both
directions. The same value relation proves equality of the two spans. Explicit
span definitions preserve the set-carrier information used by extensionality.

If the ambient dimension is d, intrinsic independent lists have length at most
d by their ambient independence. The finite set of possible lengths from 0 to d
contains 0, witnessed by the empty list. Take a maximal length and a corresponding
independent list in U. If any x in U were outside its intrinsic span, appending x
would be independent of length one larger. It is still ambient independent and
bounded by d, contradicting maximality. Thus U has a finite spanning list. One
proof-local prop represents existence at a length; no basis is selected here.

Choose a basis at the already established inherited dimension, transport its
independence and apply the ambient length bound. Both dimension value domains
remain explicit in subspace_dimension_le_ambient. The generic finite-dimensional
result supplies the inherited one separately. The real-plane consumer checks
axis/full/zero dimensions 1/2/0 and projection kernel/image finiteness. General
linear_dimension below supplies rank-nullity; further subspace dimension
theorems remain separate work.


## Finite source, kernel, image and rank-nullity

A linear map uses an arbitrary supplied target over the same field. Mapping a
finite source spanning list proves image finiteness; the inherited-subspace
theorem proves kernel finiteness. Target finiteness is an alternative sufficient
condition for image finiteness, with no implication about the source or kernel.

linear_map_rank selects the natural dimension of the inherited image, guarded
by linearity and image finite dimension. linear_map_nullity selects the natural
dimension of the inherited kernel, guarded by linearity and kernel finite
dimension. Each takes six template parameters K/F/V/X/W/Y and one ordinary map
argument T. Neither value unconditionally requires finite source.

Finite list concatenation has exactly the sum length, including empty pieces.
It splits a source basis into the extended kernel prefix and a complementary
tail. The killed-prefix spanning theorem and kernel-containing-prefix
independence theorem show that tail images form an image basis. Invariant
basis lengths then prove rank+nullity=source dimension. The decomposition and
linear-dimension modules add 21 named source theorems, three source value
families and no public or proof-local predicates.

Numeric carrier results expose N/R/C for typed arithmetic after source finite
dimension and linearity. The main equality needs only those two mathematical
hypotheses. The optional <= interfaces retain the corresponding selected
value's image/kernel finite-dimensional domain explicitly. Caller contexts
forward the necessary constructor/carrier facts across imports; they do not
assume extra finiteness for the arbitrary target.

Projection/zero/identity on the existing real plane give (rank,nullity) equal
to (1,1)/(0,2)/(2,0). Generic exact-domain calls, empty list boundaries and
missing-hypothesis/wrong-value/illegal-index controls accompany those concrete
applications. No native mathematical Obj/Fact, BT or strategy is added.
Infinite/cardinal dimensions, canonical complements, representation matrices
and further operator/spectral results are unsupported by these slices.


## Map criteria and inverse selection

The native mapping properties retain their exact domain/codomain. For linear
maps with finite kernel, zero nullity detects injectivity. Finite source gives
rank=source dimension precisely for injectivity. Finite target gives
rank=target dimension precisely for surjectivity, without requiring finite
source. With both finite, the corresponding dimension bounds yield the two
equal-dimension bijectivity criteria and dimension invariance under a supplied
linear bijection. These statements do not construct an isomorphism merely
from equality of dimensions.

Empty spans identify the zero-dimensional carrier. An inherited subspace of
ambient dimension is ambient: a subspace basis is independent in the ambient
space and therefore spans it at full dimension. Intrinsic and ambient span
equality identifies the carriers. The reverse whole-carrier dimension result
uses that common basis, without forcing equality of dependent struct objects.

The independent set-level inverse_bijection<V,W,T>(y) selects the unique
preimage of y after bijective(V,W,T). V/W may be empty sets. Unique existence
precedes selection; the two inverse identities prove inverse bijectivity.
Injectivity of T and its linearity then prove inverse linearity for arbitrary
vector spaces, without a finite-dimensional premise. There is no additional
isomorphism law certificate or overloaded inverse name.

The source adds22 named theorems including the five zero/subspace helpers and
four inverse laws, one selected-function family and no public/proof-local
predicate. Existing Field/VectorSpace, finite dimension, inherited subspaces
and rank-nullity are reused. Actual coordinate exchange and zero/empty cases
check the mathematical and selection domains. Further existence/isomorphism,
direct-sum and representation-matrix development remains open.


## Linear maps prescribed on an ordered basis

Unique coordinates reconstruct their vector and preserve addition/scalar
multiplication. Unit coefficient lists select entries; the coordinate of a
basis entry is its unit list. The formula linear_map_from_basis applies the
same coefficients to any supplied target list. This is a construction after
source-basis evidence, not an assumption that the target images form a basis.
It is linear, takes the requested basis values and is uniquely determined by
those values among linear maps. Two linear maps equal on a basis are equal.

When the target list is a basis, coordinate recovery proves both round trips,
bijectivity and agreement of the existing inverse selector with the reversed
construction. Any linear bijection also maps a supplied basis to a basis.
Chosen bases of the same finite length therefore supply an existential linear
bijection when selected dimensions agree. Necessity reuses the preceding
bijective dimension-invariance theorem; no canonical basis or default
isomorphism is selected.

The two new source families are unit_coefficients<K,F,n,j> and
linear_map_from_basis<K,F,V,X,W,Y,n,u,w>. Their ordinary arguments are a legal
coordinate index and a source vector respectively. The map allows n0 and
arbitrary target images; the unit value has no legal template index at n0.
Source and target share the same actual supplied field.

The source adds17 named theorems and19 statements with no new predicates.
Coordinates, coefficient operations, selected combinations, inherited
subspaces, finite dimension and the set-level inverse are reused. Plane
repeated-image and two-basis examples, a zero-to-plane map and zero-dimensional
isomorphism exercise the construction domains. Matrix representation and
direct sums remain separate developments.


## Internal direct sums and complementary projections

A sum vector is the sum of one member of each supplied subset. The guarded
subspace_sum value collects these vectors for two actual subspaces of the
same supplied ambient VectorSpace. Closure follows by regrouping addition
and distributing scalar multiplication. Both summands embed into the sum;
any subspace containing both contains the sum. No finite basis is involved.

is_internal_direct_sum(K,F,V,X,U,W) means both subsets are subspaces, their
sum is V and their intersection is {X.zero}. This is an internal direct sum
inside a supplied ambient space. It neither constructs an external product
space nor chooses a complement for an arbitrary subspace. Both zero-summand
orders are allowed. Trivial intersection gives uniqueness of components by
additive inverses and cancellation; full sum gives existence. Conversely,
unique existence of a pair for every vector implies full sum and trivial
intersection.

sum_decomposition<K,F,V,X,U,W>(v) selects the unique pair in U × W after
that evidence. left_projection and right_projection are the two components,
viewed as V->V maps. All four value families have six fixed template slots;
subspace_sum is a set value, the other three take one ordinary vector. The
pair is selected only after uniqueness, and neither projection requires
finite dimension or an inner product. They reconstruct the vector, are
linear, fix their own summand, annihilate the other, are idempotent and have
mutually zero composites. Their images/kernels are respectively U/W and W/U.

For finite ambient dimension, the inherited-subspace theorem supplies finite
dimension of both summands. direct_sum_dimension consumes those explicit
selected-value domains and proves dim(U)+dim(W)=dim(V) by applying rank-nullity
to the left projection. Equal subspaces have equal inherited dimension via
a common basis, so the proof does not require equality of two separately
instantiated inherited struct objects. A single theorem header which uses
those selected dimensions without their domain facts is not currently an
accepted surface; callers first release finite_direct_sum_summands.

The plane consumer checks axes and an oblique decomposition using the
diagonal plus the vertical axis. Zero/full and singleton boundaries check
that no positive dimension or nonzero summand is assumed. Overlapping or
nonspanning summands do not license a selected decomposition. External direct
sums, arbitrary complement selection, representation matrices and further
operator theory remain separate developments.

A linear idempotent supplies its own split: range/kernel are subspaces, every
v decomposes as T(v) plus the sum of v with an additive inverse of T(v), and
T(T(v))=T(v) puts that second part in the kernel. An intersection member is
both fixed by T and killed by T, so it is zero. This converse needs neither
finite dimension nor a selected complement. The public reconstruction law
uses left/right_projection, both V->V; raw tuple-coordinate ambient typing
remains a source-local step and is not an imported public contract.


## Finite subspace sums and the Grassmann formula

The subspace_sums export uses the existing six-parameter subspace_sum value
and native intersect. It introduces source theorems, not a new selected sum,
intersection, complement, dimension, predicate or scalar/vector overload.
For supplied subspaces U/W of an arbitrary ambient VectorSpace, finite
inherited dimensions imply finite inherited dimensions of U+W and U∩W.
Only one summand needs to be finite for its intersection with any subspace
to be finite. If both finite summands span V, V is finite dimensional.

The construction proceeds forward from finite generators. Concatenation
spans U+W. Bounded independent-list lengths imply finite dimension, so a
subspace contained in a finite subspace is finite without assuming finite V.
For Grassmann, choose a basis of U∩W, extend it to a basis of W, and append
only the extension tail to a basis of U. Span and coefficient uniqueness
prove that the new list is a basis of U+W, including empty lists and tails.
This gives dim(U)+dim(W)=dim(U+W)+dim(U∩W). All bases are proof-local.

The source signatures keep subspace facts for U/W/intersection/sum and the
four selected-dimension finiteness domains explicit. First establish the
intersection/sum subspace facts, then release finite_sum_and_intersection.
Calling a selected dimension without its finite-dimensional evidence is
outside its domain. sum_dimension_bounds additionally states that dim(U)
and dim(W) are real numbers: these are numerical typing premises, discharged
by finite_dimension_numeric_carriers, not additional mathematical finiteness
assumptions. Generic imported contracts exercise these exact headers.

The representative call order, after the four subspace facts and finite U/W
have been established, is shown below. The complete binder domains and
executable use are in examples/algebra/subspace_sums/contracts.lit.

<!-- litex:skip-test -->
```litex
release thm Algebra::subspace_sums::finite_sum_and_intersection(K,field,V,space,U,W)
release thm Algebra::subspace_sums::grassmann_dimension(K,field,V,space,U,W)
```

Downstream results bound intersection and sum dimensions, and characterize
dimension additivity by trivial intersection. This supports finite-dimensional
subspace calculations before choosing coordinates or complements. It does
not construct external direct sums, choose a complement, represent an
operator by a matrix or certify Litex-to-Lean support.


## Normal subgroup images and composition kernels

The normal-image checkpoint at source32/25thms adds whole/identity normality, subgroup
images, normal images under a surjective homomorphism and the composition
kernel equality. It retains the same Group, five props and one kernel
template. The image uses the native range of fn(t S) B {f(t)}, with the
actual subgroup carrier S and ambient operations. Range witnesses and
homomorphism identity/inverse preservation prove closure. For normality in
all B, surjectivity supplies a source lift of every target conjugator;
normality of S and preservation of conjugation then supply its image.

The kernel equality only unfolds composition and the two point-preimage
conditions. It applies even to non-homomorphisms and introduces no unused
source or middle Group parameter. All five source results pass on first
Session attempts and an independent strict32-statement checkpoint. All24 fresh focused checks pass: generic5, integer30, one-point17,
noncommutative17, model30, README1, legacy groups34,14 final-only refusals and
both installed layouts, with std/WiX80-file/reference agreement. Explicit
checked formation facts make the one-point instance pass in both isolated
and original Sessions; no unresolved blocker remains from that attempt.
Receipt: std-group-normal-images-acceptance-2026-10-28.json. No new native
operation, alias, rule/search/WD permission, protected state/AST, compiler
implementation or trust is introduced.


## Elementary inverse laws

The earlier group source38/31thms checkpoint added inverse identity/involution,
right-inverse uniqueness, reversed inverse-product, right-equation unique
existence and conditional inverse commutation. Existing inverse uniqueness,
left/right cancellation, associativity and identity/inverse laws supply the
proofs. The right equation's witness is b*inv(a); it solves x*a=b and does not
swap the side used by the earlier left equation. Two nested equalities need
the checked inner inverse-product identity published before outer transport.
No group law or mathematical premise is added.

This source increment adds no struct/prop/template, operation alias, native
rule/search/WD, protected state/AST, compiler implementation or trust. The
source and all 25 focused checks pass, including concrete noncommutative
values, 15 rejected final statements and both installed layouts.

## Elementary field multiplication

Distributing over zero plus zero and using additive inverses proves that zero
absorbs multiplication. Commutativity gives the other side. Multiplication by
the existing guarded inverse proves cancellation for a nonzero factor. The
two zero-product implications and nonzero-product theorem follow from these
facts. No inverse is applied at zero, and the Field structure is unchanged.
All 17 focused checks pass, including generic and real callers, 10 rejected
final statements and both installed layouts.

## Elementary field addition

Commutativity supplies right identity and left inverse from the Field axioms.
Associativity and additive inverses prove cancellation; commutativity gives
the other side. The inverse of zero and double negation follow from identity
and cancellation. All 16 focused checks pass, including nine rejected final
statements and both installed layouts.

## Field negation and multiplication

Additive cancellation gives uniqueness of an additive inverse. Distribution
and zero absorption prove the sign rule for multiplication; commutativity and
double negation give the other side and the product of two negatives. Additive
associativity and commutativity give the negative of a sum. All operands may
be zero. All 14 focused checks pass, including seven final-statement refusals
and both installed layouts.

## Guarded field inversion

The inverse of a nonzero element is nonzero, since otherwise its product with
that element would be both zero and one. Nonzero cancellation proves inverse
uniqueness and involution. Associativity and commutativity give the inverse of
a nonzero product. An imported expression involving the inverse of a product
first publishes the existing nonzero-product consequence in the calling
context; the source theorem keeps only the two nonzero-factor premises.
All 18 focused checks pass, including 11 final-statement refusals and both
installed layouts.

## Field distributivity and differences

Commutativity gives right distributivity from the existing field axiom. The
negative-factor laws then give multiplication over differences on both sides.
Additive cancellation shows that a zero difference implies equality; the
reverse follows from the additive inverse axiom. No subtraction operation
or restriction on characteristic is introduced. All 16 focused checks pass,
including nine final-statement refusals and both installed layouts.

## Field linear and affine equations

Multiplication by the guarded inverse supplies the solution of `a*x=b` when
`a` is nonzero; nonzero cancellation proves uniqueness. Subtracting the
constant term using addition and negation reduces `a*x+b=c` to that case.
Each equation has unique-existence and solution-value theorems. No new solution
selector is introduced. All 17 focused checks pass, including ten final-statement
refusals and both installed layouts.

## Zero-coefficient field equations

For any field element `x`, zero absorption gives `0*x=0` and hence
`0*x+b=b`. An unequal target cannot be attained. When the target agrees, field
zero and one are distinct solutions. The no-solution theorems quantify over
an arbitrary candidate `x`, while the two-solution theorems exhibit both
witnesses. All 16 focused checks pass, including nine final-statement refusals
and both installed layouts. Twelve earlier field callers and five group callers
also pass on the same final source snapshot.

## Two-element field instance

An explicit finite model on `{0,1}` checks addition modulo two, multiplication,
identity negation and nonzero-only inversion against the existing Field axioms.
It checks `1+1=0`, while preserving distinct zero and one, and applies the
generic inverse, distributivity and equation laws. The independently replayed
model and cross-file caller pass; all 15 focused checks include eight
final-statement refusals and both installed layouts.

## Vector space over the two-element field

The checked two-element Field supplies zero, addition and multiplication for
its scalar-line VectorSpace. The example verifies the existing VectorSpace
axioms, then checks that identity has full image and zero kernel while the zero
map has full kernel and is not injective. The generic zero-kernel criterion
applies to identity. The example proves that `1` forms a basis, the dimension
is `1`, and the zero list is not a basis. At that checkpoint, 21 focused
checks passed, including 14 final-statement refusals and both installed layouts.
The rank/nullity extension gives `(1,0)` for identity and `(0,1)` for the
zero map using the existing guarded selectors. All 29 extended focused checks
pass, including 22 final-statement refusals and both installed layouts.


## Field zero-product characterization

Zero absorption and nonzero-factor cancellation yield both directions of
`F.mul(a,b)=F.zero` iff `a=F.zero or b=F.zero`, and the two nonzero factors
of a nonzero product. The Field itself is unchanged. The actual two-element
field supplies `0*1=0` with nonzero `1`; the real-field caller also exercises
the laws. All 18 focused checks pass, including six final-only refusals and
actual/generic callers in both installed layouts.


## Group conjugation, idempotence and self-inverse elements

For `c_a(x)=G.mul(G.mul(a,x),G.inv(a))`, associativity and inverse laws give
identity, product and inverse preservation. Conjugation by `G.inv(a)` undoes
conjugation by `a` in both directions, yielding a bijective self-homomorphism.
A point is fixed exactly when it commutes with `a`; quantifying this fact gives
the abelian characterization. The Heisenberg example checks a nonidentity
conjugation without assuming commutativity.

Right identity uniqueness follows by evaluating at the existing identity;
left cancellation proves an idempotent is the identity. Inverse uniqueness
and the inverse law give `a*a=one` iff `inv(a)=a`. The additive group of the
checked two-element Field supplies a nonidentity self-inverse element. No new
Group field or operation is introduced. The conjugation and elementary batches
pass 24 and 18 focused checks respectively, including final-statement refusals
and actual/generic callers in both installed layouts.


## Unital ring foundations

A Ring supplies zero/one, an abelian-group addition/negation and associative
multiplication with both identity laws and both distributive laws. Its
nonempty carrier is explicit. Multiplicative commutativity and zero!=one are
not assumed. Additive cancellation gives inverse uniqueness and makes an
additive idempotent zero. Applying that lemma to distributivity gives left
and right zero absorption; inverse uniqueness then gives the product sign
laws. Zero=one forces every element to equal zero.

Unital addition/multiplication preservation implies preservation of zero and
negation. These facts prove that the actual zero fiber of a homomorphism is
a two-sided ideal. They also prove the ideal inverse-image theorem. The
kernel singleton criterion follows by applying a homomorphism to -y+x and
using additive cancellation, with no division or field premise. Ideal
intersection and the unit-element criterion use exactly the supplied closure
and absorption laws. A Field forgets to a Ring after proving right
multiplicative identity/distributivity from its commutative multiplication.

Dependency order: native carriers/functions -> Ring -> additive cancellation
and inverses -> zero/sign laws -> homomorphism zero/negation -> ideals and
actual kernel -> inverse images and injectivity; independently Field -> Ring
view. These are signature, definition, well-definedness and proof edges.
The README records 27 source theorems, the 33-declaration strict gate, 58 full
std-imported consumer statements and five focused source refusals. The
noncommutative concrete model is still deferred proof debt, not checked
coverage; quotient and polynomial constructions remain future work.
