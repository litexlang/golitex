# Finite combinatorics

This strict source library derives finite-map counting, the pigeonhole
principle, omitted values, equal-cardinality bijection criteria and finite-set
inclusion-exclusion. It contains 22 named source theorems and two internal
quantified closure facts, with no new values, predicates or counting operations.
Native finite_set_size and injective/surjective/bijective keep their contracts.
There are no user axioms, trust blocks or new native rules.

## Import and use

Add this beside your project's export table in litex.config:

```ini
[import std]
comb = combinatorics
```

The following complete excerpt is checked in an independent project:

```litex
have fn readme_fold(x {0, 1, 2}) {0, 1} by cases:
    case x = 0: 0
    case x = 1: 1
    case x = 2: 0

release thm comb::main::pigeonhole_collision({0, 1, 2}, {0, 1}, readme_fold)

exist x, y {0, 1, 2} st {x != y, readme_fold(x) = readme_fold(y)}
```

The [complete caller](../../examples/combinatorics/finite_maps/main.lit) obtains
the two collision inputs, proves surjectivity of the three-to-two map, checks
an omitted value for a proper inclusion and distinguishes opposite bijections
from mutual inverses. Empty finite maps and removal of a singleton are included.

## Public theorem contracts

All X,Y,A,B below are finite sets, f has the exact complete domain X and values
in Y, and g has the exact complete domain Y and values in X. No finite-cardinality
operation is defined on an arbitrary infinite set. Points lie in X.

| Theorem | Premises and conclusion |
| --- | --- |
| `injection_size_le(X,Y,f)` | Injective f implies size(X)<=size(Y) |
| `surjection_size_ge(X,Y,f)` | Surjective f implies size(Y)<=size(X) |
| `pigeonhole_collision(X,Y,f)` | size(Y)<size(X) gives distinct x,y in X with f(x)=f(y) |
| `cardinality_gap_omits_value(X,Y,f)` | size(X)<size(Y) gives y in Y outside fn_range(f) |
| `equal_size_injection_is_bijective(X,Y,f)` | Injection and equal cardinality imply bijectivity |
| `remove_one_size(X,point)` | size(X minus {point})=size(X)-1; point must belong to X |
| `surjection_collision_strict_size(X,Y,f,point,duplicate)` | Surjection, distinct points and equal images imply size(Y)<size(X) |
| `equal_size_surjection_is_bijective(X,Y,f)` | Surjection and equal cardinality imply bijectivity |
| `mutual_finite_injections_are_bijective(X,Y,f,g)` | Both injections imply equal size and both individual bijections |
| `disjoint_partition_size(X,A,B)` | union(A,B)=X and empty intersection imply size(X)=size(A)+size(B) |
| `union_size(A,B)` | Two-set inclusion-exclusion |
| `subset_difference_size(A,B)` | B subset A implies size(A minus B)=size(A)-size(B) |
| `union_bound(A,B)` | size(union(A,B))<=size(A)+size(B) |
| `subset_equal_cardinality(A,B)` | B subset A and equal finite size imply B=A |
| `cartesian_product_size(A,B)` | size(cart(A,B))=size(A)*size(B) |
| `power_set_size(A)` | size(power_set(A))=2^size(A) |
| `union_additivity_implies_disjoint(A,B)` | Additive union size implies empty intersection |
| `symmetric_difference_size(A,B)` | size of the union of the two differences is size(A)+size(B)-2*size(intersection) |
| `three_set_union_bound(A,B,D)` | Size of the three-set union is at most the sum of sizes |
| `three_set_inclusion_exclusion(A,B,D)` | Three individual sizes, minus pairwise overlaps, plus the triple overlap |
| `symmetric_difference_is_finite(A,B)` | Finiteness of the actual union of the two differences |
| `three_set_union_intersection_are_finite(A,B,D)` | Finiteness of the nested union and triple intersection |

Here size is explanatory notation for native finite_set_size, not a new Litex
operation. All theorem signatures appear in the [independent contracts](../../examples/combinatorics/finite_maps/contracts/main.lit).

The finite-set counting contracts are checked in a separate
[imported project](../../examples/combinatorics/finite_sets/contracts/main.lit).
Compound finiteness facts must be obtained explicitly across imports before
using the corresponding cardinality expressions. The following complete
excerpt transports those facts, cites the three-set formula, then counts a
three-element set's subsets:

```litex
release thm comb::main::three_set_union_intersection_are_finite({0,1,2},{2,3},{0,3})
release thm comb::main::three_set_inclusion_exclusion({0,1,2},{2,3},{0,3})
release thm comb::main::power_set_size({0,1,2})
finite_set_size(power_set({0,1,2})) = 2^finite_set_size({0,1,2}) = 2^3 = 8
```

Generic consumers can obtain the same closure facts in universal claims; the
counting theorems retain their full finite-set domains and have no extra
finiteness hypotheses. The [concrete caller](../../examples/combinatorics/finite_sets/main.lit)
checks both empty and nonempty triple overlaps, actual union size4, symmetric
difference size3, product size6, powerset size8 and all empty boundaries.
These source results reuse native closure, cardinality, arithmetic and set
extensionality; the closure exports introduce no new search strategies.

Empty X and Y remain allowed. A map from a nonempty X to empty Y cannot be
supplied. The duplicate-deletion proof constructs a local map with a smaller
complete domain; it does not retype the original f onto that domain. The
pigeonhole theorem proves existence of a pair, without selecting a canonical
pair. Opposite injections need not be mutually inverse, and equal cardinality
alone does not make an arbitrary map bijective.

The source reuses native image cardinality, inclusion bounds, strict-subset
cardinality and finite difference/union rules. surjection_size_ge already
closes by its native rule; these are named source results, not ten new kernel
mechanisms. Binomial/Pascal constructions, general fiber sums, graphs,
recurrence solving and generating functions remain future work. The original
discrete showcase is unchanged. No full course coverage is claimed.

## Verification

```bash
target/release/litex -strict -lang en -f std/combinatorics/main.lit
python3 examples/combinatorics/finite_maps/check.py
python3 examples/combinatorics/finite_sets/check.py
```

The checker covers the strict source, 50 concrete statements, ten isolated
generic contracts, README excerpt, 24 final-only semantic controls, installed
archive/shared-data discovery and full std/WiX references. No Lean, global
Cargo/release or local textbook certification is implied. math_collections.md
records the dependency spine and remaining scope.

The finite-set checker adds 62 concrete statements, 12 generic contract/closure
claims, a four-statement README excerpt and 16 final-only semantic controls.
It also checks both installed layouts and the full std/WiX payload. The source
has 24 statements: 22 named theorems and two internal closure facts. No general
indexed inclusion-exclusion, binomial coefficient or probability library is
claimed.
