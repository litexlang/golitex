# The topology of the same function

Can the identity function be continuous in one direction and discontinuous
in the other? Its formula cannot change: every point goes to itself. What
can change is which subsets of the source and target are regarded as open.

We will put two topologies on the same two-point set and examine the identity
map between them. This gives a complete counterexample to the claim that
every continuous bijection is a homeomorphism. Along the way, inverse images
will also explain why continuous functions compose.

## Two points and two choices of opens

Let $X=\{0,1\}$. Its subsets are $\varnothing$, $\{0\}$, $\{1\}$ and
$X$. The following standalone fragment from the
[complete lecture](../../showcases/topology/topology.lit) introduces the set
and checks one subset relationship. `power_set(X)` is the set of all subsets
of `X`.

```litex
have points nonempty_set = {0, 1}

0 $in points

{0} $subset points

{0} $in power_set(points)
```

A **topology** on $X$ is a collection of subsets containing $\varnothing$
and $X$, closed under arbitrary unions and finite intersections. Consider
the discrete topology $\mathcal D=\mathcal P(X)$ and the indiscrete topology
$\mathcal I=\{\varnothing,X\}$.

Every union and intersection of subsets of $X$ is again a subset, so the
discrete choice satisfies the axioms. For the indiscrete choice, a union is
$X$ if one of its members is $X$, and is empty otherwise. An intersection
of finitely many members is empty if one member is empty, and is $X$
otherwise; the empty intersection is $X$. Thus both choices are topologies.
But $\{0\}$ is open in $\mathcal D$ and is not open in $\mathcal I$.

The lecture's `TopologicalSpace` packages a carrier and its opens together
with these laws. It constructs both instances by proving their laws. Merely
naming a collection of subsets would not establish that it is a topology.

## Continuity uses inverse images

For a map $f:X\to Y$ and subset $U\subseteq Y$, its inverse image is
$f^{-1}(U)=\{x\in X:f(x)\in U\}$. This operation does not require an
inverse function. It makes sense even when $f$ is neither injective nor
surjective.

A function is continuous when every open target set has an open inverse
image in the source. The exact definition in the lecture is the following
context-dependent excerpt. The function's domain and codomain are the actual
carriers stored in the two spaces.

<!-- litex-source: ../../showcases/topology/topology.lit -->
<!-- litex:skip-test -->
```litex
prop is_topologically_continuous(A, B set, source &TopologicalSpace<A>, target &TopologicalSpace<B>, f fn(x source.carrier) target.carrier):
    forall U target.opens:
        preimage_set(f, U) $in source.opens
```

Let $i:(X,\mathcal D)\to(X,\mathcal I)$ be the identity. The target has
only two open sets. Their inverse images are $\varnothing$ and $X$, both
open in the source. Thus $i$ is continuous. It is plainly bijective.

The inverse set function $j:(X,\mathcal I)\to(X,\mathcal D)$ is also the
identity formula. However, the target now has the open set $\{0\}$.
Its inverse image is $\{0\}$, which is not open in the source. Therefore
$j$ is not continuous. One failed inverse-image test suffices to disprove
continuity; checking just the empty and whole sets would miss it.

The source checks the positive statement, bijectivity and the negative
statement separately. A **homeomorphism** requires continuity in both
directions as well as the inverse equations. Our continuous bijection fails
that stronger test.

## Why continuous functions compose

Suppose $f:X\to Y$ and $g:Y\to Z$ are continuous. For an open set
$U\subseteq Z$, continuity of $g$ makes $g^{-1}(U)$ open in $Y$.
Continuity of $f$ then makes $f^{-1}(g^{-1}(U))$ open in $X$.
Membership gives the identity

$$
x\in(g\circ f)^{-1}(U)
\iff g(f(x))\in U
\iff x\in f^{-1}(g^{-1}(U)).
$$

The two sets are equal, so the composite is continuous. The proof works for
arbitrary topological spaces, not merely our two-point examples.

This is also the structure of the checked proof: `composition_preimage`
establishes the set equality, and `continuous_composition` uses each continuity
hypothesis once. The latter's central proof steps, excerpted in their existing
local context, read as follows.

<!-- litex-source: ../../showcases/topology/topology.lit -->
<!-- litex:skip-test -->
```litex
        U $in power_set(target.carrier)
        preimage_set(g, U) $in middle.opens
        preimage_set(f, preimage_set(g, U)) $in source.opens
```

The subset is first checked to belong to the target carrier's power set.
The next two lines move it backward through the two maps. The separately
proved equality identifies that result with the inverse image under their
composite. The topology remains attached to each stage of the argument.

## Closed sets give the same test

A subset is closed when its complement in the carrier is open. Inverse
images respect relative complements:

$$f^{-1}(Y\setminus F)=X\setminus f^{-1}(F).$$

If $f$ is continuous and $F$ is closed, the left side is open, so $f^{-1}(F)$
is closed. Conversely, assume inverse images of all closed sets are closed.
For an open $U$, its complement is closed. Pull it back, then take the
complement in $X$; the identity above shows that $f^{-1}(U)$ is open.
The lecture checks both directions of this characterization. Complements
must be taken in the appropriate carriers, not in an unspecified universe.

## Exercises

1. List the continuous maps from the indiscrete two-point space to the
   discrete two-point space.
2. Is every function out of a discrete space continuous? Explain the
   inverse-image test.
3. Why is the swap $s(0)=1$, $s(1)=0$ a homeomorphism of the discrete space?

## Answers

1. Exactly the two constant maps. A nonconstant map on two points is
   bijective, so the inverse image of a target singleton is a source
   singleton, which is not open. For a constant map every inverse image is
   either empty or the whole source.
2. Yes. Every inverse image is a subset of the source, and every such subset
   is open in the discrete topology.
3. It is continuous because the source is discrete, and $s\circ s$ is the
   identity. Its inverse is therefore the same continuous map.

## Continue reading

The [longer lecture](../../showcases/topology/README.md) develops connectedness,
separation axioms, compact images and the real-line intermediate value theorem.
Its later homeomorphism package explicitly assumes a continuous inverse;
the general compact-Hausdorff continuous-bijection theorem is not established
by that package. The two-point counterexample above remains a useful test
of which hypotheses an argument actually uses.

[Previous](02-abstract-algebra.md) · [Contents](README.md) · [Next: analysis](04-analysis.md)

