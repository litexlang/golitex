# Finite sums: mathematical collections

## Source correspondence and conventions

Tao Analysis I 7.1.1 defines finite interval sums recursively and permits an
empty interval. The existing native finite_set_sum on closed_range(m,n) supplies
that total object on the exact original a:closed_range(m,n)->R. Native sum
continues to require m<=n; its nonempty bridge is explicit. Source recursion
is proved through n=m-1, including the first summand. No zero extension or
alternate overload changes the data or operation.

The author's corrections to 7.1.4 require m<=n+1 and n<=p for splitting; parts
(b)-(f) apply to every pair of integer endpoints. The module retains those
scopes, including empty pieces and every translated empty interval. For 7.1.6,
a function may be defined on a larger set U containing the finite summation
set. The corrected 7.1.14 inverse map has direction YxX->XxY.

## Integer intervals and actual translation

Extensionality proves reversed closed intervals empty. Interval containment and
an adjacent disjoint partition support singleton, recurrence and splitting.
Endpoint membership follows from the literal translated order inequalities;
the prefix inclusion and real summand carrier are established before use.
The interval algebra, comparison and triangle laws reuse existing finite-set
aggregation at the full corrected scope.

integer_interval_unshift_index is an actual complete function x->x-k from
closed_range(m+k,n+k) to closed_range(m,n). Both forward and inverse index
memberships precede its construction. Injection uses cancellation; y+k gives
surjection. Actual bijective substitution followed by pointwise callback
equality produces the literal shifted summand a(j-k), for arbitrary m,n,k in Z.

## Enumeration and arbitrary finite sets

The existing finite_set_has_bijective_index produces actual finite-sequence
data. fn_set_member exposes its complete 1..size(X) function interface.
Substitution identifies every bijective enumeration with finite_set_sum(X,f),
so two enumerations agree. Zero-length enumerations are included.

Empty/singleton values, substitution, the interval bridge, disjoint-union
splitting, addition, scaling, comparison and triangle give all nine parts of
7.1.11. The superset interfaces retain f:U->R with X subset U; U need not be
finite. Their callbacks consume only the proved range of the actual bijection.
A repeated index or a non-onto map cannot replace that bijection.

## Cartesian products and finite Fubini

cartesian_pair_swap_map constructs the actual function p->(p(2),p(1)) on
arbitrary Cartesian sets. Injection publishes equality at every tuple coordinate
before tuple extensionality; swapping back proves surjection. This includes
empty factors. Functions on products take one tuple argument.

Existing finite Cartesian flattening, the actual inverse-direction substitution
and literal callback equality establish every link: nested X-then-Y sum, flat
XxY sum, flat YxX sum with swapped data, and nested Y-then-X sum. The full
source statement has arbitrary finite factors, including either or both empty.

## Dependencies, verification and boundaries

Formation edges: exact interval carriers -> actual translation; Cartesian
projections -> actual pair swap. Proof edges: set partition -> source recurrence
and splitting; actual translation -> substitution -> literal shift; native
finite enumeration -> source enumeration value -> independence; pair swap ->
Cartesian substitution -> finite Fubini. These dependencies are acyclic.

The mathematical basis reuses native finite-set aggregation, finite enumeration,
function membership/extension, ordinary set logic and scalar arithmetic.
No new axiom, trust or native implementation is introduced. General membership
and equality evidence composition/reuse remain shared verify responsibilities.
Explicit source memberships, carriers and actual constructions are the proof tools.

Consumers check every named contract, the full README, nonempty actual
enumerations and independent values, f:R->R summed on a finite subset, a
nonreal index, negative shifts, a weighted nonsymmetric rectangle and empty
Cartesian factors. Controls reject missing domains, infinite sets, nonscalar
outputs, incorrect endpoints/values, nonbijective substitution and binary data
where tuple-unary data is required. Exact receipts and historical failed probes
remain in experiments; they do not become mathematical assumptions.
