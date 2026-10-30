# Finite combinatorics

This strict source library derives finite-map counting, the pigeonhole
principle, omitted values, equal-cardinality bijection criteria and finite-set
inclusion-exclusion, natural-valued binomial coefficients, the complex binomial
theorem and finite fiber counting. It contains 61 named source theorems in 69
source statements, including one recursive function, a zero-extended binomial
term template and internal closure facts, with no new native operations.
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
closes by its native rule. General indexed inclusion-exclusion,
recurrence solving and generating functions remain future work. The original
discrete showcase is unchanged. No full course coverage is claimed.

## Natural binomial coefficients

`binomial_coefficient(n,k)` takes exactly two natural indices and returns a
natural number. Natural indices include zero. The zero column is1; the zero
row is0 at positive columns. Positive rows and columns follow the Pascal
recursion, decreasing the row index. Entries with k>n are proved to be0.
Negative or fractional indices are outside the function's domain.

Release the imported definition before applying it or consuming the source
theorems below. This is the existing explicit object-definition contract:

```litex
release obj def comb::main::binomial_coefficient
release thm comb::main::binomial_choose_two(5)
comb::main::binomial_coefficient(5,2) = 5*(5-1)/2 = 10
release thm comb::main::binomial_symmetry(5,3)
comb::main::binomial_coefficient(5,3) = comb::main::binomial_coefficient(5,5-3) = comb::main::binomial_coefficient(5,2) = 10
comb::main::binomial_coefficient(0,0) = 1
```

Below, B abbreviates the function only in mathematical prose. The actual
public name is binomial_coefficient.

| Theorem | Natural-domain contract |
| --- | --- |
| `binomial_beyond_row_zero(n,k)` | k>n implies B(n,k)=0 |
| `binomial_diagonal(n)` | B(n,n)=1 |
| `binomial_choose_one(n)` | B(n,1)=n, including n=0 |
| `binomial_choose_two(n)` | B(n,2)=n*(n-1)/2, including n=0 and1 |
| `binomial_symmetry(n,k)` | k<=n implies B(n,k)=B(n,n-k) |
| `binomial_penultimate(n)` | Positive natural n implies B(n,n-1)=n |
| `binomial_positive(n,k)` | k<=n implies B(n,k)>0 |
| `binomial_row_monotone(n,k)` | B(n,k)<=B(n+1,k) for all natural n,k |
| `binomial_row_strict(n,k)` | k>0 and k<=n+1 imply B(n,k)<B(n+1,k) |

The full Pascal relation B(n+1,k)=B(n,k-1)+B(n,k) is checked for every
natural n and positive natural k in an independent imported consumer.
It includes n=0, k=1 and columns above the row. Defining equations are used
directly; no public evaluation or recurrence wrapper theorem is needed.
The [actual caller](../../examples/combinatorics/binomial/main.lit) also checks
the new diagonal's strict growth and equality of zero entries above the row.
The [generic contracts](../../examples/combinatorics/binomial/contracts/main.lit)
preserve every theorem's full domain and required hypotheses.

The source additionally proves `binomial_factorial_product(n,k)` and
`binomial_factorial_formula(n,k)` for natural k<=n, including row zero.
The factorial quotient follows from the product identity and factorial
positivity; it does not assume a nonzero denominator as an extra hypothesis.

`binomial_terms<n,x,y>(k)` is a complex-valued function on all natural k.
It equals B(n,k)*x^k*y^(n-k) when k<=n and zero above the row, so zero x or y
does not introduce negative powers. `binomial_expansion(n,x,y)` proves the
actual sum of these terms equals (x+y)^n for all natural n and complex x,y.
`binomial_theorem(n,x,y,terms)` also accepts an actual natural-indexed complex
function agreeing with those terms on the finite prefix; it places no
conditions on values above n. `binomial_row_sum(n)` gives 2^n, and
`binomial_alternating_row_sum(n)` gives zero for positive natural n.
Reindexing, weighted successor sums and finite-prefix extensionality are
provided as supporting source theorems.

Interpreting B(n,k) as the cardinality of k-element subsets, Vandermonde's
identity and generating functions still require separate proofs.

## Finite fibers

Fiber counts use native `preimage_set(f,{y})` and `finite_set_size`; no second
cardinality or fiber operation is introduced. Named preimage closure, empty,
codomain, union and disjointness theorems supply the set-level dependencies.
`preimage_fiber_sum(X,Y,f,S)` sums fiber sizes over a subset S of finite Y and
equals the size of its preimage. `finite_fiber_sum(X,Y,f)` specializes to Y
and equals the size of finite X, without assuming surjectivity.

`uniform_fiber_count(X,Y,f,r)` derives size(X)=r*size(Y) from uniform fibers.
Pointwise upper and lower bounds give the corresponding cardinality bounds;
`generalized_pigeonhole_fiber(X,Y,f,r)` derives a fiber larger than r from
size(X)>r*size(Y). Empty finite sets and r=0 are allowed by the signatures.
Further theorems relate positive fibers to surjectivity and fibers of size at
most one to injectivity, and prove omitted fibers empty and distinct fibers
disjoint. Functions retain their exact complete domain X.

## Verification

```bash
target/release/litex -strict -lang en -f std/combinatorics/main.lit
python3 examples/combinatorics/finite_maps/check.py
python3 examples/combinatorics/finite_sets/check.py
python3 examples/combinatorics/binomial/check.py
```

The checker covers the strict source, 50 concrete statements, ten isolated
generic contracts, README excerpt, 24 final-only semantic controls, installed
archive/shared-data discovery and full std/WiX references. No Lean, global
Cargo/release or local textbook certification is implied. math_collections.md
records the dependency spine and remaining scope.

The finite-set checker adds 62 concrete statements, 12 generic contract/closure
claims, a four-statement README excerpt and 16 final-only semantic controls.
It also checks both installed layouts and the full std/WiX payload. That earlier
suite covers the 34-statement baseline: 31 named theorems, one natural-valued
function and two internal closure facts. General indexed inclusion-exclusion and the finite
probability library remain unfinished.

The binomial checker covers 39 concrete statements,14 independent generic
statements, the six-statement README excerpt,21 final-only controls, both
installed layouts and the same complete std/WiX payload. Its controls include
omitting definition release separately from false mathematical claims and
invalid indices. These suites describe the earlier baseline validation.

The 2026-10-30 resumed extension gate passes all 69 source statements and an
independent 71-statement strict imported consumer, including full-domain
contracts for all 30 added theorems. It checks (1+i)^5=-4-4i, an actual
five-element map with fiber sizes 2,3,0, empty source/codomain cases and uniform
zero fibers. A fresh Session replays all 71 positive statements and rejects
20 final-only false claims or missing hypotheses at their intended phases.
At the user's subsequent pause request, this round's receipt, imported test
project, journals and pinned executable were removed. These numbers record
the historical checkpoint. The earlier installed-layout and
packaging checks were not rerun. Subset counting and Vandermonde remain open.
