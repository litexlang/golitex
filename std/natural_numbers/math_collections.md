# Natural recursion: mathematical dependencies

## Construction and uniqueness

Native natural numbers and decreasing-index function definitions construct
`natural_recursion<S,start,step>`. At index zero it returns the supplied member
of `S`. At a positive index it applies `step(n-1,...)` to the preceding value.
Both the predecessor index and the recursive result have their required
carriers. The step is allowed to depend on the index.

`natural_recursion_equations` exposes the ordinary zero/successor presentation.
The successor index's membership and lower bound are explicit source facts.
`is_natural_recursion` records those equations for an arbitrary complete
`N -> S` function. Induction proves pointwise uniqueness. A two-candidate
pointwise proof and complete-domain function extensionality establish unique
existence of the actual function, rather than an assumed sequence witness.

## Discrete existence

The unique predecessor of a positive natural is `a-1`; cancellation proves
uniqueness. Zero is outside this theorem's domain.

Euclidean existence reuses the native integer decomposition
`n=q*quot(n,q)+n%q` and `0<=n%q<q`. If its quotient were negative, integrality
would make it at most `-1`, forcing the nonnegative dividend below zero. Thus
the native integer quotient is natural. These actual native expressions are
the witnesses; no parallel quotient or remainder operation is introduced.

For uniqueness, a smaller quotient is at least one whole divisor smaller.
The bounded remainder cannot make up that difference, contradicting equality
of the dividend. Reversing the comparison gives equal quotients; cancellation
then gives equal remainders. This additional law supports later positional
digit constructions.

## Source and acceptance boundaries

The dependency order follows Tao, *Analysis I*, 2.1.16, 2.2.10 and 2.3.9.
The existing native number systems are reused; this module does not prove
the underlying foundational arithmetic or introduce another model of `N`.
Independent uses include both numerical closed forms and a carrier of sets.
The public contracts require a complete closed step, a valid initial member,
natural indices and a positive division modulus. See the README for the
recorded strict verification boundary.
