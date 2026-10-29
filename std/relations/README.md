# Relations and order

This module provides bundled equivalence relations and partial orders on an
actual carrier contained in an ambient set. It contains 21 checked source
theorems, two structures, seven predicates and three templates. Empty carriers
are permitted. Import `relations` and alias its `main` export.

## Interfaces

| Interface | Meaning and main results |
| --- | --- |
| `EquivalenceRelation<Ambient>` | Carrier and ordered-pair subset with reflexivity, symmetry and transitivity. |
| `equivalence_class<A,E>(x)` | Actual related-element subset; contains x and is nonempty. Related elements have equal classes; equal classes imply related elements. |
| `equivalence_classes<A,E>` | Image of the class map, with no chosen representatives. Classes are equal or disjoint, cover the carrier and form a partition. |
| `is_partition(Carrier,blocks)` | Blocks are subsets of Carrier, nonempty, cover Carrier and are pairwise equal or disjoint. The empty family partitions the empty carrier. |
| `PartialOrder<Ambient>` | Carrier and ordered-pair subset with reflexivity, antisymmetry and transitivity. Totality is not assumed. |
| `is_least_element`, `is_greatest_element` | A supplied point belongs to the subset and is below/above every point. Such a point is unique and minimal/maximal. |
| `is_minimal_element`, `is_maximal_element` | No strictly smaller/larger subset point. Restricting to a smaller subset preserves any of these four properties when the point remains in it. |
| `is_monotone`, `is_order_embedding` | Order preservation, and additionally order reflection for an embedding. Both compose; order embeddings are injective. |
| `diagonal_pairs<X>` | The actual diagonal relation on X. Checked constructors supply equality equivalences, discrete partial orders and universal equivalences. |

Template names are used as `\rel::equivalence_class<A,E>(x)` after a
configuration alias `rel = relations::main`. Call the constructor theorem
before binding the corresponding `(carrier,pairs)` tuple. Imported theorems
must be called explicitly; ambient facts are not merged. Open a bound structure
with `release struct def value` when its coordinate bridges are needed.

## Validation and boundaries

Run `python3 std/relations/validation/check.py` from the repository root.
The strict main source has 33 accepted declarations; the imported consumer has
43 accepted statements, including arbitrary-carrier callers, equality/universal
relations on two points, the empty carrier, extrema and composition. The checker
requires every statement preceding each final refusal to succeed. It rejects
a two-point universal relation as a partial order, an empty partition block,
a minimal point incorrectly claimed least, and a class call outside its carrier.

No representative selector, converse partition construction, quotient algebra,
linear order, lattice, supremum or order-topology result is supplied yet.
See [math_collections.md](math_collections.md) for dependencies.
