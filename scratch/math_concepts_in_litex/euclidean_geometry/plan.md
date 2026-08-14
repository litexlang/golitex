# Plan: Euclidean Geometry

## Reader promise

This file should let a reader see a mathematical world grow from points and
segments into one classical construction. The picture should remain mentally
visible while every step is machine-checkable. The first release chooses one
honest analytic model rather than mixing synthetic and coordinate foundations.

## Foundational decision

The plane is `R^2`. Geometry is represented by coordinate-invariant or
coordinate-transparent predicates built from displacement vectors, dot
products, determinants, and squared distance.

This decision is reversible only at high cost: a synthetic axiomatic plane has
different primitive objects, incidence assumptions, and proof dependencies.
The analytic choice is recommended for the current Litex stage because it can
produce complete checked constructions now and reuse existing real arithmetic.
The file must state this boundary prominently and must not claim to formalize
Euclidean geometry independently of coordinates or real-number facts.

## Mathematical boundary

Included:

- points in `R^2` and displacement vectors;
- dot product, determinant, and squared distance;
- collinearity, parallelism, perpendicularity, and segment congruence;
- affine lines and incidence;
- circles as loci of fixed squared distance;
- triangle congruence at least through SSS in the analytic model;
- one clear notion of betweenness/on-segment when needed; and
- explicit geometric constructions with coordinate witnesses.

Explicitly excluded:

- a Hilbert/Tarski/Euclid synthetic axiom system in the same file;
- three-dimensional, spherical, hyperbolic, projective, or affine geometry as
  separate subjects;
- angle orientation machinery beyond what one flagship theorem needs;
- trigonometric geometry and coordinate bashing as an exercise collection;
- continuity/topology-based geometric existence theorems; and
- treating a diagram or numeric check as proof of the general result.

The first-release stop line is Euclid I.1: construct an equilateral triangle
on any nondegenerate segment using an explicit vertex and prove the three
segment congruences. Later Euclid propositions belong only if they reuse and
stress the same compact interface rather than opening another textbook.

## Internal architecture

1. **Plane carrier**: `points = R x R`.
2. **Vector calculations**: displacement, dot, determinant, squared distance.
3. **Relations/loci**: collinear, parallel, perpendicular, congruent segment,
   line, circle, and equilateral triangle.
4. **Reusable laws**: distance coordinate formula, nonnegativity, symmetry,
   zero-distance identity, and rotation/norm preservation.
5. **Construction layer**: an explicit equilateral vertex on directed base
   `a -> b`.
6. **Flagship theorem**: for `a != b`, that vertex forms an equilateral
   triangle with base `a,b`.

## Main theorem chain

```text
R^2 point carrier
  -> displacement vector
  -> dot/determinant
  -> squared distance and collinearity
  -> segment congruence and equilateral-triangle predicate
  -> 60-degree rotation norm identity
  -> explicit equilateral vertex
  -> equal squared distances from both endpoints
  -> Euclid I.1 existence theorem
```

Lines and circles are supporting interfaces, not prerequisites for I.1. They
should not delay the primary chain.

## Scratch example ladder

1. `distance_sq((0,0),(3,4)) = 25` -- current tracer; a recognizable numeric
   fact consumes the generic coordinate formula.
2. `(2,2)` lies on `x-y=0` -- first locus membership example.
3. A horizontal and vertical displacement have zero dot product -- first
   perpendicularity example.
4. Rotation by 60 degrees preserves squared norm -- key algebraic bridge.
5. Construct the equilateral vertex of the segment `(0,0)` to `(2,0)` --
   concrete visual preview.
6. Euclid I.1 for arbitrary distinct `a,b` -- flagship theorem with an
   explicit existential witness.

## Modeling decisions

- `vec`, `dot`, `det`, `distance_sq`, `line`, `circle`, and
  `equilateral_vertex` are callable functions or set-valued functions.
- collinearity, congruence, perpendicularity, incidence laws, and
  equilateral-triangle status are `prop` relations on supplied points.
- use squared distance in the core to avoid unnecessary square-root
  well-definedness; actual distance is added only when a consumer needs it.
- line and circle are actual sets because callers need membership and
  intersection statements; `is_line` remains a property of a proposed set.

## Lean comparison scene

Use Euclid I.1 or the 60-degree norm identity in a concrete `R x R` model on
both sides. Lean should use mathlib's available Euclidean/inner-product
interfaces where idiomatic; Litex should show the small domain language and
explicit witness. Disclose that Lean supports much more general normed and
inner-product spaces. The Litex claim is accessibility of this chosen model,
not superior geometric foundations.

## Acceptance gates

- Independent release-runner success with no direct `trust` in the main
  construction.
- The analytic foundation and its real-number dependencies are explicit.
- Every public geometric relation has at least one actual use.
- Euclid I.1 proves a general existential theorem, not only one coordinate
  instance.
- Nondegeneracy assumptions are visible.
- The proof distinguishes the diagram/preview from the general theorem.
- No synthetic theorem name is attached to a result with materially weaker
  analytic premises or conclusion.

## Expected downstream consumers

This is the strongest visual/public demo. Its vector and dot-product layer also
provides a concrete consumer for the later linear-algebra abstractions, but the
scratch projects remain independent until the shared interface is stable.
