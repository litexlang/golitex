# General topology

This strict source library develops open-set spaces, continuous maps,
homeomorphisms, connectedness, separation axioms and compactness over arbitrary
carriers, including empty ones. It exports one structure, eight value/function
families, seventeen predicates and 73 named source theorems in 102 statements.
There are no user trust blocks, user axioms, new kernel objects or reserved
theorems.

## Import and use

Add this beside your project's `[export]` table in litex.config:

```ini
[import std]
top = topology
```

The package exports `main`; use `top::main::name` or configure `[alias] top = top::main` for `top::name`.
This complete excerpt is checked in an independent project:

```litex
release thm top::main::discrete_topology_laws({0, 1})
have sample_space &top::main::TopologicalSpace<{0, 1}> = ({0, 1}, power_set({0, 1}))
release thm top::main::identity_is_homeomorphism({0, 1}, sample_space)
```

The [foundations caller](../../examples/topology/foundations/main.lit)
compares discrete and indiscrete topologies on {0,1}, proves the reverse
identity discontinuous, checks a swap homeomorphism and covers empty carriers.

## Spaces and maps

`TopologicalSpace<Ambient set>` stores `carrier power_set(Ambient)` and
`opens power_set(power_set(carrier))`, with direct empty/whole, binary
intersection and arbitrary-union laws. Ambient only bounds the actual carrier.

| Interface | Meaning |
| --- | --- |
| `\discrete_space<X>` | `(X,power_set(X))`, X any set |
| `\indiscrete_space<X>` | `(X,union({{}},{X}))`, including empty X |
| `\identity_map<X>(x)` | x for x in X |
| `\restricted_map<X,Y,f,K>(x)` | f(x) on the actual domain K, with K subset X |
| `$is_closed(A,space,F)` | F lies in the actual carrier and has open relative complement |
| `$is_topologically_continuous(A,B,source,target,f)` | Open preimages; f maps the actual carriers |
| `$has_closed_preimages(A,B,source,target,f)` | Every closed target subset has closed preimage |
| `$is_homeomorphism(A,B,source,target,f,g)` | Both continuous directions and both inverse equations |
| `$is_connected(A,space)` | A disjoint open separation has an empty piece |
| `$is_clopen(A,space,F)` | F is open and closed |
| `$has_only_trivial_opens(A,space)` | Each open is empty or the carrier |
| `$has_only_trivial_clopen(A,space)` | Each clopen is empty or the carrier |
| `$has_separating_open(A,space,x,y)` | An open contains x and excludes y, in that order |
| `$is_T0(A,space)` | Distinct points have a separating open in at least one orientation |
| `$is_T1(A,space)` | Every ordered distinct pair has a separating open |
| `$is_Hausdorff(A,space)` | Distinct points have disjoint open neighborhoods |
| `$is_compact_subset(A,space,K)` | Every arbitrary indexed open cover has a finite subcover of K |
| `$is_compact_space(A,space)` | The actual carrier is compact |

Names take the caller's `top::main::` prefix. The two space families each have
one set template slot and no ordinary arguments. identity_map has one slot
and one point argument. restricted_map has four slots X,Y,f,K and one point
argument in K. It constructs a new complete input domain; f itself is not
retyped onto a proper subset. K may be empty. Native compose(g,f), preimage_set
and fn_range remain the underlying operations.

Cite discrete_topology_laws(X) or indiscrete_topology_laws(X) before typing a
constructed tuple. Imports do not merge ambient proofs. Named space values
also need the checked explicit tuple equations shown in the foundations caller
for membership/field projection. Bare template family names do not support
release obj def. Restriction function-domain inspection uses native
fn_set_member with its exact complete domain when required.

## Continuous maps, homeomorphisms and connectedness

The original 28 theorems cover construction laws; empty/whole closed and
clopen sets; closed finite unions; preimage identity/composition/complement/
union/intersection/empty/whole; continuous identity/composition and both
closed-preimage criteria; maps from discrete and to indiscrete spaces;
homeomorphism identity/inverse/composition/bijectivity; connectedness and
clopen characterization; connected surjective images and indiscrete spaces.
[Their generic callers](../../examples/topology/foundations/contracts/main.lit)
retain the original signatures. Inverse continuity belongs to the
homeomorphism definition; the compact-to-Hausdorff theorem below now derives
it under its stated hypotheses.

## Separation and compactness

This independently checked excerpt constructs a compact Hausdorff finite space:

```litex
release thm top::main::discrete_topology_laws({0, 1})
have demo &top::main::TopologicalSpace<{0, 1}> = ({0, 1}, power_set({0, 1}))
demo.carrier = {0, 1}
demo.opens = power_set({0, 1})
power_set(demo.carrier) = power_set({0, 1}) = demo.opens
release thm top::main::discrete_is_Hausdorff({0, 1}, demo)
release thm top::main::finite_subsets_are_compact({0, 1}, demo, demo.carrier)
by def $top::main::is_compact_space({0, 1}, demo)
```

[The complete new caller](../../examples/topology/separation_compactness/main.lit)
uses a proper subset image and a noninjective map, verifies empty restrictions,
and distinguishes R with its indiscrete and discrete topologies. The former is
compact and not Hausdorff; the latter is not compact, proved using a singleton
cover indexed by all of R. This explicitly exercises infinite index sets.
A compact image inside the noncompact target is paired with proved nonsurjectivity.

| Separation/compactness theorem | Premises/result |
| --- | --- |
| `Hausdorff_implies_T1`, `T1_implies_T0`, `Hausdorff_implies_T0` | The separation implication chain |
| `T1_implies_closed_singletons`, `Hausdorff_implies_closed_singletons` | Closedness of each supplied actual point |
| `closed_singletons_imply_T1` | All actual singletons closed implies T1 |
| `discrete_is_Hausdorff` | opens equals the carrier's full power set |
| `two_point_subset_of_Hausdorff_is_closed` | union({x},{y}) closed; x=y is allowed |
| `homeomorphism_preserves_Hausdorff` | Homeomorphism and Hausdorff source |
| `trivial_opens_with_distinct_points_not_T0` | Trivial opens and two supplied distinct points |
| `restriction_range_monotone` | K subset L gives f(K) subset f(L) |
| `empty_is_compact`, `singleton_is_compact` | No separation premise |
| `union_of_compact_subsets_is_compact` | Both supplied subsets compact |
| `finite_subsets_are_compact` | Any finite subset, in any topological space |
| `continuous_image_of_compact_is_compact` | Continuous f and compact K give compact fn_range(f restricted to K) |
| `continuous_surjection_preserves_compactness` | Compact source, continuous surjection gives compact target |
| `homeomorphism_preserves_compactness` | Homeomorphism and compact source |
| `trivial_open_space_is_compact` | Trivial opens, without a finiteness premise |

[Independent contracts](../../examples/topology/separation_compactness/contracts/main.lit)
list all 19 theorem signatures and the restriction value/type contracts. Points
and compact subsets belong to the actual carrier, even when Ambient is R and
the carrier is {0,1}. Compactness imposes no finite-index-cover restriction;
the finite set is the selected subcover's index set. A compact subset need not
be closed without Hausdorff separation. Surjectivity is essential for a whole-
target conclusion, while injectivity is not required for compact images.

The additional source below supplies subspace topology, closed compact-subset
theorems in Hausdorff spaces and the full compact-to-Hausdorff continuous-
bijection theorem. Product and quotient topology, generated metric topology
and path foundations remain future work. The original lecture is unchanged.

## Compact sets, closed maps and continuous inverses

The new proofs retain arbitrary indexed covers, arbitrary actual carriers and
empty spaces. They do not assume a finite cover index set or a nonempty space.

| Theorem | Exact main result |
| --- | --- |
| `closed_intersection_of_compact_is_compact(A,space,K,F)` | Compact K and ambient-closed F imply compact `intersect(K,F)` |
| `closed_subset_of_compact_is_compact(A,space,K,F)` | Compact K, closed F and F subset K imply compact F |
| `compact_subset_of_Hausdorff_is_closed(A,space,K)` | Hausdorff space and compact K imply closed K |
| `compact_to_Hausdorff_continuous_map_is_closed(A,B,source,target,f)` | A continuous map from compact source to Hausdorff target is a closed map; no injection or surjection premise |
| `inverse_preimage_equals_forward_image(X,Y,f,g,F)` | Mutually inverse f,g give `preimage_set(g,F)=fn_range(restricted f to F)` |
| `inverse_of_closed_bijection_is_continuous(A,B,source,target,f,g)` | A closed map with supplied two-sided inverse g has continuous g |
| `compact_Hausdorff_inverse_is_homeomorphism(A,B,source,target,f,g)` | Compact source, Hausdorff target, continuous f and the two inverse equations imply homeomorphism; inverse continuity is proved |
| `compact_Hausdorff_bijection_has_continuous_inverse(A,B,source,target,f)` | Compact source, Hausdorff target, continuous bijective f give an actual function g with the homeomorphism relation |

`is_closed_map` requires every closed subset of the source carrier to have
closed image, formed using the existing actual restriction function and its
range. The inverse-existence theorem proves unique preimages, constructs the
inverse with `have fn ... by exist!`, proves both inverse equations and then
its continuity. It does not take a continuous inverse as a premise.

After the four hypotheses are established, the exported invocation is:

```litex
release thm top::main::compact_Hausdorff_bijection_has_continuous_inverse(A,B,source,target,f)
```

The [full imported consumer](validation/main.lit) constructs the discrete
three-point space and the cycle 0->1->2->0, proves its bijectivity and continuity,
then obtains the theorem's inverse. Its values are 1->0, 2->1, 0->2 and its
continuity is verified. The consumer also checks continuous-inverse existence for the empty-to-empty
map.

Supporting results include `union_of_two_opens_is_open` and
`open_neighborhood_criterion`. The latter proves a supplied subset open when
each of its points has an open neighborhood contained in that subset.

## Relative intersections and subspaces

`is_in_space_intersection(A,space,Index,cover,J,x)` means x lies in every
`cover(index)` for index in J. The cover is a function from arbitrary Index to
space.opens, and J is a subset of Index. The value
`\space_indexed_intersection<A,space,Index,cover,J>` is the corresponding
subset of space.carrier. Its construction permits arbitrary J. If J is empty,
the value is space.carrier; `finite_space_intersection_is_open` requires J
finite and proves the value open. The empty, insertion and equal-index-set
identities are exported as `space_indexed_intersection_empty`,
`space_indexed_intersection_insert` and
`space_indexed_intersection_equal_indices`. This relative construction does
not assign a universal-set value to native `family_intersect({})`.

For K a subset of the actual space carrier and U a subset of K,
`is_relative_open(A,space,K,U)` means U is `intersect(K,V)` for an actual
ambient open V. Its associated constructions are:

| Interface | Actual construction |
| --- | --- |
| `\subspace_open_family<A,space,K>` | All relatively open subsets of K |
| `\subspace_space<A,space,K>` | `(K,subspace_open_family)`, of type `TopologicalSpace<K>` and with actual carrier K |
| `\subspace_inclusion<A,space,K>` | The function on the constructed carrier with value x in space.carrier |

`relative_empty_is_open`, `relative_carrier_is_open` and
`relative_intersection_is_open` establish the elementary trace laws.
`intersect_traces` is the underlying three-set intersection identity.
`subspace_open_family_closed_under_union` handles arbitrary unions;
`subspace_topology_laws` certifies the actual tuple as a topology. The proof
uses all valid ambient extensions, without asking for a function choosing one
extension per relative open.

| Theorem | Result |
| --- | --- |
| `subspace_inclusion_preimage(A,space,K,U)` | Inclusion preimage of U is `intersect(K,U)` |
| `subspace_inclusion_is_continuous(A,space,K)` | The constructed inclusion is continuous |
| `continuous_map_restricts_to_subspace(A,B,space,target,K,f)` | Continuous f remains continuous after composition with inclusion |
| `subspace_of_Hausdorff_is_Hausdorff(A,space,K)` | Hausdorff separation passes to the constructed subspace |
| `compact_subset_gives_compact_subspace(A,space,K)` | Ambient compactness of K makes its subspace compact |
| `compact_subspace_gives_compact_subset(A,space,K)` | Compactness of that subspace gives ambient compactness of K |

The last two statements establish the usual compact-subspace equivalence.
They keep arbitrary cover indices and include empty K. The restriction theorem
uses native `compose(f,inclusion)` with the complete constructed domain; it
does not assert a smaller domain for the original f. Constructor memberships,
projection equations and point-carrier facts are proved explicitly in the
generic imported consumer before nested constructed-space goals are checked.

## Verification

```bash
python3 std/topology/validation/check.py
```

The source-owned checker passes 102 strict source statements, 123 imported
consumer statements and 12 final-only refusals in a fresh persistent strict
Session. Every new theorem has a full-domain generic caller. Concrete cases
include the three-cycle and its obtained inverse; a proper and an empty
subspace; both compactness directions; an infinite cover index set with empty
or finite selected indices; a valid infinite relative-intersection object;
an infinite compact indiscrete space with a compact singleton proved not
closed; and the empty-space inverse theorem.

The refusals cover each missing hypothesis of the inverse-existence theorem,
missing inverse equations, missing closedness, missing Hausdorff separation,
an outside subspace carrier or inclusion argument, missing finite-subfamily
evidence, an incorrect empty relative-intersection value, and an attempted
retyping of a larger-domain map. Every refusal requires an accepted prefix.

Existing external example projects under `examples/topology/` retain the older
foundation and separation/compactness demonstrations. This std-only batch
adds no installer, Lean or repository-wide release certification. See
[the mathematical spine](math_collections.md) for the dependencies.
