# General topology

This strict source library develops open-set spaces, continuous maps,
homeomorphisms, connectedness, separation axioms and compactness over arbitrary
carriers, including empty ones. It exports one structure, four value/function
families, fourteen propositions and 47 named source theorems in 66 statements.
There are no user trust blocks, user axioms, new kernel objects or reserved
theorems.

## Import and use

Add this beside your project's `[export]` table in litex.config:

```ini
[import std]
top = topology
```

The package keeps one main export, preserving existing `top:::name` calls.
This complete excerpt is checked in an independent project:

```litex
release thm top:::discrete_topology_laws({0, 1})
have sample_space &top:::TopologicalSpace<{0, 1}> = ({0, 1}, power_set({0, 1}))
release thm top:::identity_is_homeomorphism({0, 1}, sample_space)
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

Names take the caller's `top:::` prefix. The two space families each have
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
retain the original signatures. A continuous bijection still requires inverse
continuity for homeomorphism.

## Separation and compactness

This independently checked excerpt constructs a compact Hausdorff finite space:

```litex
release thm top:::discrete_topology_laws({0, 1})
have demo &top:::TopologicalSpace<{0, 1}> = ({0, 1}, power_set({0, 1}))
demo.carrier = {0, 1}
demo.opens = power_set({0, 1})
power_set(demo.carrier) = power_set({0, 1}) = demo.opens
release thm top:::discrete_is_Hausdorff({0, 1}, demo)
release thm top:::finite_subsets_are_compact({0, 1}, demo, demo.carrier)
by def $top:::is_compact_space({0, 1}, demo)
```

[The complete new caller](../../examples/topology/separation_compactness/main.lit)
uses a proper subset image and a noninjective map, verifies empty restrictions,
and distinguishes R with its indiscrete and discrete topologies. The former is
compact and not Hausdorff; the latter is not compact, proved using a singleton
cover indexed by all of R. This explicitly exercises infinite index sets.
A compact image inside the noncompact target is paired with proved nonsurjectivity.

| New theorem | Premises/result |
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

Subspace/product topology, metric/path foundations, closed compact-subset
theorems in Hausdorff spaces, and the full compact-Hausdorff continuous-
bijection theorem remain future work. The original lecture is unchanged.

## Verification

```bash
target/release/litex -strict -lang en -f std/topology/main.lit
python3 examples/topology/foundations/check.py
python3 examples/topology/separation_compactness/check.py
```

The projects check independent positive callers/contracts/README excerpts,
22 original and 28 new final-statement rejections, installed archive/shared-data
discovery and std/WiX file/component references. No global Cargo/release or
Lean certification is implied. math_collections.md records the mathematical
dependency graph.
