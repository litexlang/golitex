# Real interval existence: mathematical spine

## Source and role

OpenStax [Calculus Volume 1, section 2.4, Theorem 2.11](https://openstax.org/books/calculus-volume-1/pages/2-4-continuity)
is the source anchor for intermediate values. Its Checkpoint 2.26 supplies the
polynomial x^3-x^2-3*x+1 on [0,1]. The polynomial x^3-x-1 on [1,2] is a
separate library application. The curriculum positions are C04 and U02.2.06–07.
This does not claim coverage of every continuity exercise or an entire chapter.

## Objects, relations and exact domains

The input is an actual complete function from a closed interval to R.
The interval and function spaces, real arithmetic, native relative continuity
and least-upper-bound certificates are reused. No replacement continuity
predicate, root selector, native operation or bundled structure is introduced.
Each public theorem name has one fixed contract.

The ordering a<=b is encoded in b's parameter domain. Relative continuity at
an endpoint retains the closed interval as the function's actual domain.
The weak intermediate-value result permits a=b. The interior result requires
strict value bounds, which already preclude that degenerate situation.
A supplied function on a larger domain must be restricted as a new function.
This is exact carrier construction, not a cast or compatibility assertion.

Intermediate-value existence belongs in a theorem. A relation describing a
candidate root would not prove it exists, and a canonical selected root would
need an additional meaningful selection rule. The constant-function controls
show why uniqueness must not be inferred here.

## Forward proof dependencies

Native completeness -> a least upper bound for the nonempty set of interval
points where f(x)<=level. The left endpoint witnesses nonemptiness, and the
right endpoint bounds the set. Its supremum c remains in the closed interval.

Continuity at c supplies an epsilon-delta neighborhood. If f(c)<level, move a
small positive distance to the right: continuity keeps the value below level,
contradicting the upper bound c. If f(c)>level, a set member arbitrarily close
on the left has a value above level, contradicting its defining inequality.
Thus f(c)=level. Explicit inequalities retain their actual real carriers and
supply the small translations required by the current local search rules.

The strict ordered theorem -> endpoint cases -> weak ordered theorem.
Negating the function and value handles the opposite endpoint order without
assuming global monotonicity. Strict minimum/maximum bounds exclude both
endpoints and yield the interior theorem. Equal endpoints are handled by the
weak branch, not by division by interval length.

## Uses, evidence and boundaries

The independent cubic example establishes an interior zero without guessing
its numerical value. The source polynomial exercises reversed endpoint values.
The imported callers also cover a decreasing linear function, either endpoint,
a singleton interval and a constant zero function with roots at both 0 and 1.
All four general signatures have independent imported theorem calls.

Before cleanup, strict source, imported and README gates, followed by a fresh
positive replay and final-only refusal checks, checked these interfaces. Rejecting a wider
function without a restriction is an API-domain check; the discontinuity,
outside-level and false-uniqueness cases are distinct mathematical boundaries.
Native real completeness and continuity control are reused foundations, not
new foundational proofs delivered by this source file. No user assumptions,
trust commands or native changes are used.

The rest of C04 still needs actual attained extrema, uniform
continuity and explicit real/metric/topological bridges. These dependencies
remain visible in the paused course plan; the intermediate-value increment
does not stand in for those results.

## Continuous image bounds and future attained extrema

Continuous-image boundedness is now proved on the same actual closed
interval. OpenStax [section 4.3, Theorem 4.1](https://openstax.org/books/calculus-volume-1/pages/4-3-maxima-and-minima)
states attained extrema and leaves its proof to analysis; the library must
supply that proof rather than introduce it as an assumption.

A general local upper-bound theorem follows from continuity. The source uses
the mathematical relation that f(t)<=M whenever t in [a,b] satisfies t<=x.
The set of x whose prefix has such an upper bound
contains a and is bounded by b. At its supremum c, a local continuity bound
and a previously bounded prefix show the prefix through c is bounded. If c<b,
the same local bound extends it to the right, a contradiction. Thus the whole
image is bounded above. Applying that theorem to the negative function gives
the lower bound. Bounds are real witnesses, not selected optimal values.
The endpoint reciprocal, equal to zero at zero and 1/x elsewhere on [0,1],
is proved unbounded; continuity is necessary for the general guarantee.
The focused source/imported/README and fresh-Session boundary gates passed
8/75/7 statements and ten controls before cleanup. The acceptance fixtures,
runner and local verification workspace were removed at the user's request;
these are historical results. Attainment and uniform continuity remain
separate existence proofs.
