# Linear-map interface inventory

## Accepted inverse and dimension increment

The public module registers inverse.lit (10 statements), dimension.lit (5)
and identity_compositions.lit (4). The strict final target replays all 15
predecessors. The independent caller passes 72 statements and five required-
premise refusals in a fresh Session. See validation/.ladr/acceptance.json.

- inverse::is_two_sided_inverse(V,W set,T FnV W,S FnW V)/4 means both identities.
  Empty sets are permitted subject to the supplied function carriers.
- inverse::is_linear_isomorphism(K nonempty_set,F Field<K>,V nonempty_set,
  source VectorSpace<K,F,V>,W nonempty_set,target VectorSpace<K,F,W>,T FnV W)/7
  means T is linear and has an actually linear reverse with both identities.
- inverse::are_linearly_isomorphic(K,F,V,source,W,target)/6 means an isomorphism exists.

Inverse theorems: two_sided_inverse_implies_bijective/4, two_sided_inverse_unique/5,
bijective_has_selected_two_sided_inverse/3, linear_isomorphism_is_bijective/7,
linear_bijection_is_isomorphism/7, linear_isomorphism_inverse_is_linear/7 and
linear_isomorphism_inverse_unique/8. The selected function remains
Algebra::linear_criteria::inverse_bijection, with proved identities, linearity and
uniqueness. No new inverse Obj is introduced.

Dimension theorems: equal_dimension_injection_is_linear_isomorphism/7,
equal_dimension_surjection_is_linear_isomorphism/7,
linear_isomorphism_preserves_finite_dimension/7,
equal_finite_dimensions_are_linearly_isomorphic/6 and
linearly_isomorphic_finite_spaces_have_equal_dimensions/6. Both spaces must be
finite dimensional. The injection/surjection criteria require equal dimensions;
dimension zero is included. General bijection/isomorphism equivalence is unrestricted.

Composition theorems: equal_dimension_left_inverse_is_right_inverse/8,
equal_dimension_right_inverse_is_left_inverse/8,
two_sided_inverse_has_identity_compositions/4 and
identity_compositions_are_two_sided_inverse/4. Use the existing map_compose and
identity. ST acts on V; TS acts on W. Both one-sided implications retain both
linearity hypotheses, both finite-dimensional hypotheses and equal dimensions.

The arbitrary Field contract includes actual R/C. The caller checks multiplication
by 2 and i, equality of explicit inverses with the existing selector, and both
zero-dimensional coordinate spaces. Five controls reject missing two-sided inverse,
bijectivity and equal-dimension evidence and preserve context. Source/configuration/
executable hashes are recorded. A receipt note corrects an initial helper-default
hash; both actual gates executed the unchanged task-owned acbc6e6d9bdb9188bf2fb57bdbac22b8981486df925a53cf1154ab2c80d6de2e binary.

LADR 3.59/3.60/3.61/3.63/3.65/3.68/3.69/3.70 are accepted. source_concordance.json
records the author's 30 October 2026 PDF and 3.68 erratum, retaining historical
catalogue locators. No native operation, rule, BT name/arity, strategy, AST,
Env/Runtime, parser, verifier, compiler, Lean bridge, trust or axiom changed.

## Accepted Algebra reuse audit

The 33-claim Algebra-only fixture and three clean retained-context refusals accept
3.1/3.4/3.7/3.10/3.11/3.13/3.14/3.15/3.16/3.18/3.19/3.21/3.22/3.24. It verifies actual
unique basis-image extension (including natural length zero), composition and
zero, both kernel and range definitions/subspace laws, both zero-kernel criteria,
injectivity/surjectivity definitions, both full-range directions, rank-nullity
and dimension barriers. Only the source is assumed finite dimensional for the
direct kernel/image dimension formula; the target may be infinite dimensional.
No new public Obj, predicate or theorem is added by this reuse fixture. See
validation/.ladr/existing_acceptance.json. The A-B ledger is 84/119.

## Accepted source space interfaces

space.lit registers 46 statements after 19 inverse/dimension predecessors.
The strict canonical gate, 121-statement independent saved caller and five
retained-context refusals all pass. Items 3.2/3.5/3.6 are accepted in
validation/.ladr/space_acceptance.json. This checkpoint has 65 source statements;
the four registered composition declarations bring the current module to 69.

Eight new source Obj families, all with fixed mathematical contracts:

- pointwise_map_add<K,F,X set,W,target>(S,T FnX W) -> FnX W;
  pointwise_map_smul<K,F,X,W,target>(a K,T FnX W) -> FnX W;
  pointwise_map_zero<K,F,X,W,target>(x X) -> W. X may be empty.
- vector_function_space<K,F,X,W,target> -> VectorSpace<K,F,FnX W>, defined by
  the proved pointwise zero/add/smul tuple.
- linear_map_carrier<K,F,V,source,W,target> -> power_set(FnV W), exactly the
  literal subset satisfying the existing Algebra linearity predicate.
- linear_map_add<K,F,V,source,W,target>(S,T carrier) -> carrier;
  linear_map_smul<K,F,V,source,W,target>(a K,T carrier) -> carrier.
- linear_map_space<K,F,V,source,W,target> -> VectorSpace<K,F,carrier>, defined
  by the proved existing zero-map/new addition/new scalar-multiplication tuple.

K, V and W are nonempty, F is the supplied Field<K>, and source/target are the
supplied VectorSpaces. The ambient function domain X is an arbitrary set. No
finite-dimensional assumption enters any construction. R/C are actual cases;
finite coordinate dimension zero is included.

Public source theorems expose pointwise closure, exact membership introduction
and elimination, nonemptiness, original function carriers, and the fact that the
linear-map carrier is a subspace of the ambient function space. The actual
space_add/space_smul/space_zero interfaces identify its fields with the proved
operations. Function-carrier and pointwise-result interfaces let a caller bind
an actual result as FnV W before evaluation. Direct nested application of an
operation returning the named carrier remains an authoring goal-WD miss; no
specialized verifier path was added to hide it.

The canonical constructor replaces an alias-valued prototype with an explicit
proved tuple. Its VectorSpace axioms reuse the ambient pointwise space and
verified closure, rather than unproved structure assumptions. That committed
prototype replacement justified a restart/replay; normal failures retained the
live Session. Journals preserve both. The namespace-generation mistake and its
cleanly rejected startup are preserved separately; the corrected 46-statement
source passes. Explicit scalar-space zero-field facts resolve concrete zero
calculations. Items 3.2/3.5/3.6 are accepted for this increment.

## Accepted composition laws

composition.lit has four checked source theorems: map_composition_associative/7,
map_composition_identities/3, composition_distributes_over_outer_sum/9 and
composition_distributes_over_inner_sum/10. They use the existing map_compose and
identity and the proved pointwise function sum. Associativity and identities
hold for arbitrary functions on nonempty sets. The outer-sum law requires only
the target VectorSpace; the inner-sum law requires the outer function linear
between the supplied spaces. These general contracts include the original
all-linear-map book hypotheses. No Obj, prop, native operation or reserved
name is introduced here. The four-statement canonical target passes after 65 predecessors. The independent
67-statement caller and three clean retained-context refusals also pass; 3.8 is
accepted in validation/.ladr/composition_acceptance.json. The module has 69 source
statements. Section 3A is complete; the A-B ledger is 84/119.

Remaining: representing matrices, reconstruction, rank correspondence, systems
and change of basis. Complete FTA also remains unfinished. No new native rule,
strategy, BT name/arity, AST, Env/Runtime, parser, verifier, compiler, Lean bridge,
trust or axiom is introduced by these source increments.
