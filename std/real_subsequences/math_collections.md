# Real subsequences: mathematical collections

## Purpose and conventions

The mathematical spine follows Tao Analysis I 6.6.1, 6.6.4-6.6.6 and 6.6.8.
Preserve literal complete integer-tail domains and finite-real epsilon limits.
The source zero-start formulation is included, while the existing std
arbitrary-integer-start convention remains available in every principal result.
No alternate number system, infinite limit point or general metric compactness
is introduced.

## Index maps, data and the source relation

An index map is actual data f:Tail(substart)->Z. Its defining proposition owns
both range >=start and adjacent strict increase. The given-map relation adds
exact b(n)=a(f(n)); existential closure gives the source subsequence relation.
The formula-defined real_tail_index_pullback constructs the complete real data
for valid maps. A relation alone would not construct data, and an arbitrary
reindexing would omit the source strict-order condition. Quantitative growth
f(n+t)>=f(n)+t follows by induction; pairwise growth follows at t=k-n.

The actual identity and composition maps prove reflexivity and transitivity.
Growth transports any source epsilon cutoff to the subsequence domain, proving
limit preservation. The identity subsequence gives the reverse universal-limit
criterion. These are full relations on complete functions, rather than
assumptions about their eventual limits.

## Least members and actual recursive selection

is_least_natural_member(X,n) is the candidate minimum relation. For every
nonempty X contained in N, ordinary induction proves existence: without a
least member all members would exceed every natural bound, including themselves.
Antisymmetry proves uniqueness. The canonical least_natural_member function is
then introduced from the proved unique-existence universal. Nonemptiness and
the natural-subset carrier belong to its own input domain. The relation,
existence theorem and actual selected value have different mathematical roles.

For a finite limit point L, real_tail_close_natural_offsets(epsilon,lower)
constructs the actual natural subset of offsets beyond lower whose original
values are epsilon-close to L. The limit-point witness property proves this set
nonempty. Its least member is an actual close offset, not an assumed convergent
index. Named exact local sets expose defining membership facts without changing
the set-valued function or its mathematical contract.

The existing index-dependent natural recursion starts at an offset close within
one. Its step selects a strictly larger offset close within 1/(k+2). Actual
recursion equations give strict growth and error <=1/(k+1). Adding the original
start and shifting k=n-substart constructs real_tail_limit_point_indices on any
complete subsequence tail. Pulling back the original data constructs
real_tail_limit_point_subsequence. An Archimedean epsilon cutoff proves its
convergence, and the given-map equation proves it is a source subsequence.
No convergence condition is hidden in eligibility or index validity.

## Limit points and Bolzano-Weierstrass

A convergent subsequence gives arbitrarily late original values close to its
limit: quantitative index growth exceeds any requested original cutoff.
This proves the reverse of the constructed limit-point/subsequence equivalence.

For a bounded real tail, existing extended-extrema results prove its limsup is
finite and is an actual limit point. The construction therefore returns a
complete subsequence converging to that finite limsup. The existential theorem
returns the real limit, actual subsequence relation and epsilon limit together;
it does not presume the original sequence converges.

## Dependency map and build order

Signature/definition edges: native integer/real tails -> actual maps and data ->
given-map relation -> source existential relation. Proof edges: induction ->
quantitative growth -> composition and limit preservation -> universal criterion.
Existence/uniqueness/selection edges: natural well-ordering -> unique minimum ->
canonical minimum. Definition and proof edges: actual close-offset sets +
limit-point witnesses -> nonempty eligible sets -> selected offsets + existing
natural_recursion -> actual increasing indices -> actual pullback -> convergence.
Import/proof edges: bounded finite limsup + its limit-point theorem + the
construction -> Bolzano-Weierstrass. Existing native arithmetic, induction,
real completeness and source libraries are the reused foundation; there is no
new trusted or axiomatic boundary.

The source relation and limit criterion precede construction. Natural
well-ordering is a supporting prerequisite before 6.6.6's omitted exercise proof.
All subsequent construction nodes precede the Bolzano-Weierstrass consumer.

## Interface obligations and checked uses

Keep range and strict order in index validity; preserve unconditional value
agreement and complete original domains. Keep the least-member relation
separate from its guarded canonical function. Literal functions and original
index memberships remain proof obligations. For selected limits, publish
convergence before using the partial scalar selector. Public mathematical names
have one fixed contract.

Independent uses include both finite limit points of (-1)^n, actual selected
subsequences at starts 0 and -4, and a constant parent starting at -3 with a
shifted subsequence starting at 5. The latter checks source/native limit
transport, relation composition and exact index values. Canonical selection
computes the minimum of N as zero. False controls reject repeated/decreasing or
out-of-range indices, nonexistent zero subsequences, invalid radii, empty or
non-natural minimum inputs, unbounded Bolzano use and wrong finite limits.
No mathematical proof hole is left in these source results. General expression
membership and evidence reuse belong to shared verify; source facts and exact
public interfaces are used here without a native repair.
