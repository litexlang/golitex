# Source-anchored chapter specifications

Planning increments, 2026-10-30. This document expands 21 clusters from the
[curriculum map](curriculum-map.md). The full nine-school/26-undergraduate-lane
goal remains in force. These specifications are an implementation entry point,
not a replacement for the other 154 clusters.

Requirement rows remain planning contracts unless their evidence column
records checked implementation. S02.2 and the degree-counting part of U08.1 now have checked checkpoints
described below. Other rows remain planned unless marked as partial evidence. Historical source
excerpts are audit anchors, rather than fresh verification by themselves.
An excerpt's presence, a historical README receipt, or absence of a direct
`trust` token does not establish current chapter acceptance. Implemented names
and dependencies are owned by the linked source modules; no kernel contract
is introduced by this document.
Symbols such as q, Delta, r_plus and I below are mathematical specifications,
not newly declared Litex identifiers.

## Sources and mapping limits

| Cluster | Primary source anchor | Mapped scope and explicit boundary |
| --- | --- | --- |
| S02.2 | OpenStax, *Intermediate Algebra 2e*, [9.2 completing the square](https://openstax.org/books/intermediate-algebra-2e/pages/9-2-solve-quadratic-equations-by-completing-the-square) and [9.3 quadratic formula](https://openstax.org/books/intermediate-algebra-2e/pages/9-3-solve-quadratic-equations-using-the-quadratic-formula) | Real quadratic solving and discriminant cases. Vieta and total coefficient classification are explicit library supplements, not claims about those sections' complete contents. The complex-root branch is retained under S07.5. |
| S04.2 | Euclid, [Book I in Joyce's edition](https://mathcs.clarku.edu/~djoyce/elements/bookI/bookI.html), I.4–I.12 and I.26 | Triangle congruence, isosceles facts and elementary constructions. Median/centroid concurrency is a school-geometry supplement. An analytic coordinate model is not an axiomatic formalization of all Euclid. |
| U02.2 | MIT 18.100A Fall 2020, [readings and lectures](https://ocw.mit.edu/courses/18-100a-real-analysis-fall-2020/pages/lecture-notes-and-readings/), Lectures 14–17; Lebl *Basic Analysis I*, sections 3.1–3.4 as assigned there | Interval continuity, extrema, intermediate values and uniform continuity. Derivative/MVT and FTC dependencies belong to the later U02 clusters. |
| U04.5 | Axler, [*Linear Algebra Done Right*, fourth edition](https://linear.axler.net/), Chapters 6–7; author lists an English PDF dated 28 October 2026 | Inner products through orthogonality, projections, adjoints, spectral results and SVD. Textbook scalar-linearity conventions must be reconciled with the current native convention. Infinite-dimensional Hilbert-space results belong to U20. |
| U10.1 | Beck, Marchesi, Pixton and Sabalka, [*A First Course in Complex Analysis*, version 1.6](https://matthbeck.github.io/complex.html), [author PDF](https://matthbeck.github.io/papers/complex.pdf), sections 1.4 and 2.1–2.4 | Plane topology, complex limits/continuity, differentiability, Cauchy–Riemann and constant functions. Analyticity equivalence, contour integration and residue theory remain later U10 obligations. |
| U11.1 | Lebl, [*Notes on Diffy Qs*, live HTML Chapter 1](https://www.jirka.org/diffyqs/html/fo_chapter.html), sections 1.1–1.5 and 1.8, accessed 2026-10-30 | Integrals, separation, linear equations, substitution and exact equations. Autonomous dynamics, numerical methods and first-order PDE are cross-mapped to U11.5, U16.5 and U12.1. General Picard existence/uniqueness remains U11.4. |
| U15.1 | Pishro-Nik, [*Introduction to Probability, Statistics, and Random Processes*, 8.1.1](https://www.probabilitycourse.com/chapter8/8_1_1_random_sampling.php), live author textbook accessed 2026-10-30 | Random samples, sample means and order statistics. The finite construction and sample-variance work below are explicit prerequisites/supplements. WLLN/CLT cross-reference U14.4; inference procedures remain U15.2–U15.4. |
| S04.1 | Euclid, [Book I in Joyce's edition](https://mathcs.clarku.edu/~djoyce/elements/bookI/bookI.html), definitions and I.1–I.3/I.10–I.12 | Incidence and elementary constructions in the existing analytic-plane interpretation. I.9 angle bisection is shared with S04.2. This is not a claim to formalize all synthetic axioms. |
| U02.3 | MIT 18.100A [Lectures 19–20](https://ocw.mit.edu/courses/18-100a-real-analysis-fall-2020/pages/lecture-notes-and-readings/), Lebl sections 4.1–4.3; OpenStax [Taylor remainder](https://openstax.org/books/calculus-volume-2/pages/6-3-taylor-and-maclaurin-series) and [L'Hopital](https://openstax.org/books/calculus-volume-1/pages/4-8-lhopitals-rule) | MVT, Taylor and derivative applications; exact regularity and limit variants must be stated individually. Infinite Taylor representation remains U02.5. |
| U02.4 | MIT 18.100A [Lectures 20–22](https://ocw.mit.edu/courses/18-100a-real-analysis-fall-2020/pages/lecture-notes-and-readings/); OpenStax [improper integrals](https://openstax.org/books/calculus-volume-2/pages/3-7-improper-integrals) | Riemann construction, FTC, calculation methods and limiting integrals. Proper Riemann integrals, ordinary improper integrals and principal values retain distinct contracts. |
| U04.2 | Axler [fourth edition](https://linear.axler.net/), Chapter 3 matrix representations and Chapter 9 determinants; standard elimination is an explicitly added computational obligation | The textbook's R/C presentation is generalized explicitly to the supplied-field scope of existing std coordinates. Linear systems, row operations and determinants remain actual construction obligations. Characteristic/minimal polynomials remain U04.3, reusing U05.3. |
| U05.3 | Judson, [*Abstract Algebra: Theory and Applications*](https://twjudson.github.io/aata.html), [Chapter 17 and 18.2](https://twjudson.github.io/aata-files/aata-html/aata-toc.html), author HTML edition listed as updated August 2025 | Formal polynomials, division, irreducibility and factorization domains. Ring, integral-domain and field hypotheses must remain separate. The source's degree(0)=-infinity convention needs an explicit interface decision. |
| U07.1 | Levin, [*Discrete Mathematics: An Open Introduction*, third edition, 1.1–1.5](https://discrete.openmathbooks.org/dmoi3/ch_counting.html) | Finite sequences, subsets, combinations, permutations, bijections and repeated-choice counting. General indexed inclusion-exclusion remains U07.2. |
| U14.1 | Pishro-Nik, [joint PMF 5.1.1](https://www.probabilitycourse.com/chapter5/5_1_1_joint_pmf.php), [independence 5.1.3](https://www.probabilitycourse.com/chapter5/5_1_3_conditioning_independence.php) and [joint families 6.1.1](https://www.probabilitycourse.com/chapter6/6_1_1_joint_distributions_independence.php) | Finite and countably discrete laws, marginalization and joint independence. Infinite families/process existence and continuous laws remain later U14 obligations; finite support alone does not close countable discrete probability. |
| U03.2 | Lebl, *Basic Analysis II*, [several-variable differentiation and 8.5 inverse/implicit theorems](https://jirilebl.github.io/ra/html/sec_svinvfuncthm.html) | Total differentiation and local existence theorems on actual open real domains. Scalar and vector native operators retain their different fixed contracts; local invertibility does not imply a global inverse. |
| U05.1 | Judson, [*Abstract Algebra: Theory and Applications*, Chapters 3–6, 9–11 and 14–15](https://twjudson.github.io/aata-files/aata-html/aata-toc.html) | Group foundations, cosets/quotients, isomorphisms, actions and Sylow. Existing std group laws and homomorphism results are starting material, not work to duplicate. |
| U08.1 | Levin, [definitions and degree counting, third edition 4.1](https://discrete.openmathbooks.org/dmoi3/sec_gt-intro.html) and [trees, 4.2](https://discrete.openmathbooks.org/dmoi3/sec_trees.html) | Walks, paths, connectedness, trees, spanning trees and degree counting. Empty-graph/tree conventions and the current ordered-arc storage need explicit bridges. |
| U09.2 | Hatcher, [*Notes on Introductory Point-Set Topology*](https://pi.math.cornell.edu/~hatcher/Top/TopNotes.pdf), constructions of spaces | Bases, subspaces, products, disjoint unions and quotient topology. Arbitrary-product inhabitedness is not obtained by assuming representatives/choice. |
| U13.1 | Axler, [*Measure, Integration & Real Analysis*](https://measure.axler.net/), 2A–2D; author PDF dated 12 June 2026; Norris, [*Probability and Measure*](https://www.statslab.cam.ac.uk/~james/Lectures/pm.pdf), extension-theorem supplement | These graduate-level references are used only for the listed foundational measure chapter, not their whole syllabi. Infinite measure values, sigma-additivity and Lebesgue construction remain necessary; the general extension proof is explicitly supplementary to Axler's route. |
| U16.4 | Driscoll and Braun, [*Fundamentals of Numerical Computation*](https://fncbook.com/), Chapters 5 and 9, with [author's course/text description](https://tobydriscoll.net/fnc/) | Polynomial/piecewise interpolation, approximation and quadrature with error bounds. Exact-real truncation error is distinct from floating-point stability in U16.1. |
| U17.1 | Boyd and Vandenberghe, [*Convex Optimization*](https://stanford.edu/~boyd/cvxbook/), Chapters 2–3 and basic optimality in Chapter 4 | Convex sets/functions, separation and foundational optimality. KKT, duality, algorithms and further program classes stay in U17.2–U17.5. |

Section headings and the stated mathematical interfaces were inspected; these
are not full source-to-every-exercise translations. Before accepting a cluster,
finish its exact theorem/exercise mapping, including the supplements identified
above. Pin a source version when implementation begins if the live HTML changes.

## Shared modelling and evidence rules

Values and actual constructions must be usable as values/functions. Independent
relations use `prop`; bundled structures retain their data and laws directly.
Expose a selected value only under its genuine definition domain or after
proved unique existence. No relation may hide the desired construction in its
premises. Preserve empty/zero cases where the mathematics permits them.

For each requirement, record its exact source, semantic role, domain, dependency
kind, intended caller and acceptance state. The 210 identifiers below are
stable mathematical obligations, not 210 new theorems or a progress percentage.
Checked evidence for the explicit real-equation requirements below does not
certify all exercises or any complete course.

At the user's 2026-10-30 pause request, this execution round's added test
fixtures and temporary verification material were removed. Counts and
checked-use annotations below record the historical passing checkpoint;
they do not imply that the removed suites remain available. The original
graph fixtures and the mathematical source are retained.

## S02.2 — Quadratic equations and real-root classification

**Planning baseline.** [Manual R14](../docs/Manual.md) contains a source proof of a
completed-square bound for positive leading coefficient. Its core expression
is reproduced here as a historical documentation excerpt:

```litex
a*x^2+b*x+c = a*(x+(b/a)/2)^2+(c-(b^2/a)/4)
```

This identity provides a proof route. Its documented positive-a bound is not
the complete root classification for arbitrary real coefficients. The original
planning audit found no dedicated std quadratic-equation chapter interface.
The new [real_quadratics](real_quadratics/README.md) now supplies the checked
source construction below using ordinary real arithmetic and principal roots.
Its clean gates accept 28 source statements, 65 full imported statements, an
independent nine-statement excerpt and 16 final-only refusals. All 23 named
theorems have full-domain imported callers. OpenStax examples 9.21 and 9.27
and the empty real solution set of 9.24 are checked; Vieta/converse and total
coefficient cases remain explicitly labelled library supplements.

| Requirement | Semantic role | Mathematical contract | Direct dependencies  Checked evidence |
| --- | --- | --- | ---  --- |
| S02.2.01 | Function | The real polynomial value q(a,b,c,x)=a*x²+b*x+c for all real coefficients and x. A general polynomial datatype is not required to express this fixed-degree function. | Native real arithmetic, signature/definition.  `quadratic_value` in [source](real_quadratics/main.lit). |
| S02.2.02 | Function/value | Delta=b²-4*a*c, always real; no leading-coefficient or sign restriction belongs to this value itself. | .01 coefficients, definition.  `quadratic_discriminant` in [source](real_quadratics/main.lit). |
| S02.2.03 | Set-valued construction | The actual real solution set {x in R:q(a,b,c,x)=0}, defined for all a,b,c, including the zero polynomial. | .01 and set builders, definition.  `quadratic_solutions` in [source](real_quadratics/main.lit). |
| S02.2.04 | Guarded values | Formula branches (-b±sqrt(Delta))/(2*a), only for a!=0 and Delta>=0. If ordered roots are exposed, use center -b/(2*a) and radius sqrt(Delta)/(2*abs(a)); a minus sign in the numerator alone does not select the smaller root when a<0. | .02, nonzero denominator and principal-root WD.  Both guarded formula values; positive/negative-leading order callers and invalid-domain controls. |
| S02.2.05 | Theorem | For a!=0, q=0 iff (2*a*x+b)²=Delta. Supply the algebraic identity and both implication directions. | .01–.02, arithmetic proof.  `quadratic_square_identity`, `quadratic_root_implies_square`, `quadratic_square_implies_root`. |
| S02.2.06 | Theorem | For a!=0, Delta<0 gives no real root, Delta=0 one distinct root, Delta>0 exactly two distinct roots; prove existence and exhaustiveness, not just substitution. | .04–.05 and real square-root laws, proof.  `quadratic_negative_discriminant`, `quadratic_repeated_solution_set`, `quadratic_two_distinct_roots`, and exhaustive `quadratic_solution_formula`. |
| S02.2.07 | Theorem | For a=0: b!=0 gives {-c/b}; b=0,c!=0 gives the empty set; b=c=0 gives R. Do not evaluate a quadratic-root selector in this branch. | .03, elementary linear solving, proof.  `linear_solution_set`, `nonzero_constant_solution_set`, `zero_polynomial_solution_set`. |
| S02.2.08 | Theorem | Vieta sum/product and q(x)=a*(x-r_minus)*(x-r_plus), including coincident branches for Delta=0. Distinct-root cardinality is separate from multiplicity. | .04–.06, proof.  `quadratic_vieta` and `quadratic_factorization`, including repeated-root callers. |
| S02.2.09 | Theorem/method | Converse sum/product data yield the corresponding factorization and complete root set; factoring, completing the square and the formula agree on their domains. | .05–.08, proof.  `quadratic_vieta_converse` and `quadratic_solution_set_from_vieta`, including r=s. |
| S02.2.10 | Use requirement | Complete a parameter-case analysis and an elementary application, with all degenerate branches and admissible-domain checks. | .06–.09; application assumptions, use. Both generic parameter-family branches, linear/repeated special values and attained fixed-sum product bound were checked before the requested test cleanup; see [the module checkpoint](real_quadratics/README.md). |

**Intended tracer.** Classify every real root of
`(m-1)*x²+2*x+1=0`. For m=1 the root is -1/2; for m=2 it is the repeated
root -1; for m<2,m!=1 there are two distinct real roots; for m>2 there are none.
At m=0 the ordered roots are 1-sqrt(2),1+sqrt(2). These expectations now have
checked imported evidence, including both unrestricted parameter branches.
The negative-leading example confirms that formula-minus is the larger root.

**False boundaries.** Reject two distinct roots at Delta=0, a real square root
of a negative discriminant, division by a=0, and a sign-independent claim that
the plus-numerator branch is the larger root. Complex roots remain a separate
named domain contract under S07.5; do not overload a real selector to supply them.

**Implemented dependency order.** Arithmetic/domain facts -> .01–.05 ->
.06–.07 -> .08–.10. Public names live only in `real_quadratics`; the full
solution formula uses a union of singleton roots so the zero-discriminant case
retains the same theorem. No complex root, general polynomial datatype or
native verifier change was introduced. The exact real-equation contract above
has checked evidence; rationality classifications, nonstandard-form exercise
audits and the other S02 clusters remain outside this bounded checkpoint.

## S04.2 — Triangles, congruence and elementary constructions

**Current anchors.** [Coordinate definitions](../showcases/2D_Geometry/geo_definitions.lit)
and [geometry proofs](../showcases/2D_Geometry/geo.lit) already contain triangle,
angle, SAS/SSS/ASA/AAS, median and perpendicular material. For example:

```litex
prop is_triangle(a, b, c cart(R, R)):
    det2(vec(a, b), vec(a, c)) != 0
```

The existing `sss_congruence` theorem derives corresponding dot equalities
from three squared-side equalities. It is useful evidence to audit; its name
does not by itself provide an actual isometry construction or the whole school
chapter. The source's angle relation also retains a sign clause in addition
to squared-cosine data. Do not discard that clause when extracting an interface.
The smaller [Euclid I.1 showcase](../showcases/math_concepts_in_litex/2_euclidean_geometry/main.lit)
provides an explicit equilateral vertex. These are outside std and were not
rerun or edited in this phase.

| Requirement | Semantic role | Mathematical contract | Direct dependencies |
| --- | --- | --- | --- |
| S04.2.01 | Objects/relations | Real-plane points, noncollinear ordered triangles, side lengths/squared lengths and angle incidence. Keep triangle nondegeneracy in the actual concept definition. | Existing coordinate model, signature/definition. |
| S04.2.02 | Relation and construction | Congruence with fixed vertex correspondence, allowing reflections; prove its connection to an actual distance-preserving plane map rather than choosing orientation silently. | .01; affine/isometry construction and proof. |
| S04.2.03 | Relation/bridge | Unoriented angle equality with distinct rays and sufficient sign information; prove any dot/length formulation equivalent on its stated domain. | Positive side lengths, norm/angle facts, WD/proof. |
| S04.2.04 | Theorem | SSS yields the congruence consequences and the promised correspondence/isometry bridge. Extract the useful existing scalar proof without pretending a definition is the theorem. | .01–.03 and existing SSS proof, proof. |
| S04.2.05 | Theorem | SAS uses the included angle and its adjacent sides; derive the third side and the remaining corresponding angles. | .03, cosine identity, proof. |
| S04.2.06 | Theorem | ASA/AAS congruence with correct matching and nondegeneracy; prove the angle-sum/side bridges needed by the chosen representation. | .03–.05 and angle facts, proof. |
| S04.2.07 | Actual construction/results | Reuse the S04.1.07 midpoint; construct the centroid and prove incidence/uniqueness, median concurrency and the 2:1 ratio. Mere predicates on supplied candidate points are insufficient. | S04.1.07, affine coordinate formulas and nondegenerate triangles, construction/proof. |
| S04.2.08 | Construction uses/results | Reuse S04.1.07 feet and perpendicular bisectors for triangle sides; prove the triangle incidence/orthogonality and uniqueness consequences. | S04.1.07, nondegenerate triangles, proof/use. |
| S04.2.09 | Actual constructions/results | An internal angle-bisector ray and its geometric property; appropriate isosceles/base-angle results and construction uses. Distinguish a ray from its supporting line. | .03, positive lengths and side selection, construction/proof. |
| S04.2.10 | Use requirement | A congruence application, reflected-triangle example, median/foot construction and a concrete SSA ambiguity. | .04–.09, use/false-boundary controls. |

**Intended tracers.** Use A=(0,0),B=(4,0),C=(0,3). Construct its centroid
(4/3,1) and the foot of C on AB, and compare it to the reflected triangle
with C'=(0,-3). Congruence must survive reflection although the signed
determinants have opposite signs.

**False boundary.** SSA does not give general congruence. Take A=(0,0),
C=(2*sqrt(3),2), and B=(2*sqrt(3)±sqrt(5),0). Both triangles have AC=4,
BC=3 and angle A=30 degrees, but different AB. Also test a repeated base
point and a collinear triple at interfaces requiring nondegeneracy.

**Build order.** Audit existing coordinate contracts -> .01/.03 -> scalar
congruence bridges -> actual isometry/construction obligations -> applications.
Reusing the established real-plane model is the candidate route. No new
axiomatic geometry model or public namespace is committed by this specification.

## U02.2 — Continuous functions on intervals

**Current anchors.** Native real continuity introduction/projection rules live
in [continuity.rs](../src/execute/execute_by_stmt/builtin_thm/continuity.rs).
In particular, this existing Rust contract consumes uniform continuity and
concludes ordinary continuity (whitespace condensed):

```rust
FnUniformContinuous => {
    req.push(global(rt, f.clone(), FunctionContinuityProperty::UniformContinuous));
    vec![global(rt, f, FunctionContinuityProperty::Continuous)]
}
```

It is not the closed-interval theorem that derives uniform continuity from
continuity. [metric_sequences](metric_sequences/README.md) supplies real
completeness and [topology](topology/README.md) supplies general compactness
results, but using the latter requires the correct real-topology bridge.
No native rule is proposed or changed here.

| Requirement | Semantic role | Mathematical contract | Direct dependencies |
| --- | --- | --- | --- |
| U02.2.01 | Actual function restriction | For a<=b and [a,b] contained in the actual real domain D of f, construct its restriction to I=[a,b]. Preserve equality of values; do not assert a smaller function domain for the original f. | Exact function carriers, signature/definition. |
| U02.2.02 | Reused relations/results | Native continuity at a point/on the actual domain, pointwise introduction/projection, algebra and composition with all nonzero/range hypotheses. Inventory before adding source wrappers. | Existing real-continuity contracts, reuse/proof. |
| U02.2.03 | Theorem/domain cases | Restriction continuity, one-sided endpoint interpretation, constant functions and the singleton interval a=b. | .01–.02, proof. |
| U02.2.04 | Theorem | A continuous real function on a nonempty closed bounded interval has bounded image, with a genuine finite real bound. | Real completeness or compactness bridge, proof. |
| U02.2.05 | Existence theorem | Both image extrema are attained by actual points of I. The minimum/maximum value is unique; an attaining point need not be unique. | .04 and completeness/compactness, existence/proof. |
| U02.2.06 | Existence theorem | Every real value between f(a) and f(b) is f(c) for some c in I, regardless of endpoint-value order; include equality and a=b. | .01–.03 and interval completeness, existence/proof. |
| U02.2.07 | Existence theorem | Strict opposite endpoint signs with a<b give an interior zero. Do not conclude uniqueness from the intermediate-value hypotheses. | .06, order, proof. |
| U02.2.08 | Theorem | Continuity on I implies uniform continuity on I; use the actual restricted function and the existing uniform-continuity relation. | Sequential compactness of this closed bounded real interval, derived from real completeness, proof. |
| U02.2.09 | Theorem/transport | Continuous images and extrema are compatible with the intended real/metric/topological representations, once those bridges are proved. Record each bridge rather than presuming all notions interchangeable. | .01–.08 and explicit topology/metric bridges, proof/import. |
| U02.2.10 | Use requirement | An IVT zero, an attained-extrema example and a uniform-continuity use, plus failed hypotheses on open/unbounded/discontinuous examples. | .05–.09, use/controls. |

**Intended tracers.** Obtain an interior zero of t³+t-1 on [0,1]. For t² on
[-1,2], exhibit minimum 0 at 0 and maximum 4 at 2. These are existence/value
uses; selecting a canonical minimizing point for every continuous function is
not part of the contract.

**False boundaries.** On (0,1), f(t)=t need not attain its supremum and g(t)=1/t
is continuous but unbounded and not uniformly continuous. A jump from -1 to 1
need not take the value 0. These controls separate missing hypotheses, not
verifier bugs. A source proof through supremum or subsequences is a candidate
route; a route through general topology must first establish its real-space
and interval-compactness dependencies.

## U04.5 — Inner products through spectral decompositions

**Current anchors.** [VectorSpace](algebra/vector_space.lit) and the
[basis/dimension layer](algebra/README.md) already support abstract linear
algebra. Native finite products expose the reserved signature
`inner_product_linear_right(u,v,w,a,b,n)` in
[matrices.rs](../src/execute/execute_by_stmt/builtin_thm/matrices.rs). Its
existing Litex call shape is shown schematically, not as a standalone program:

```litex
release thm inner_product_linear_right(u,v,w,a,b,n)
```

The contract is linearity in the second argument: <u,a*v+b*w>=a*<u,v>+b*<u,w>.
For complex scalars the first argument is conjugate-linear. Axler's first-slot
linearity convention needs an explicit translation when reusing that source's
statements; neither convention may silently change the native operation.
Native Cauchy–Schwarz and norm results are reusable finite-coordinate facts,
not by themselves proofs for every abstract inner-product space.

| Requirement | Semantic role | Mathematical contract | Direct dependencies |
| --- | --- | --- | --- |
| U04.5.01 | Bundled structure | An inner product on an actual real/complex vector space, with positivity, definiteness and a fixed linearity convention directly in its laws. Positivity is not assumed for a vector space over an arbitrary field. | Existing vector spaces and standard scalar structures, signature/law. |
| U04.5.02 | Function/bridge | Derived real norm and metric, including the zero vector and dimension zero; prove compatibility with native coordinate products/norms for the concrete models. | .01, principal square root and norm laws, WD/proof. |
| U04.5.03 | Theorem | Cauchy–Schwarz, triangle inequality and the appropriate equality characterizations for the abstract structure. | .01–.02, positivity/proof. |
| U04.5.04 | Relations/results | Orthogonality, orthogonal complements, independence of orthonormal families and finite-dimensional direct-sum decompositions. | .01–.03 and existing finite basis theory, definition/proof. |
| U04.5.05 | Actual algorithm/construction | Gram–Schmidt on an ordered independent family, giving an actual orthonormal family with the same successive spans. Handle an empty family; normalization requires each proved nonzero residual. | .03–.04, finite recursion and residual positivity, existence/WD. |
| U04.5.06 | Actual construction/theorem | Orthogonal projection onto a finite-dimensional subspace and its unique best-approximation vector. In least squares, distinguish that vector from coefficient solutions, which are unique only with the relevant injectivity/full-rank hypothesis. | .04–.05, projection existence/uniqueness, proof. |
| U04.5.07 | Actual constructions/results | Finite-dimensional adjoints, their uniqueness and matrix/conjugate-transpose correspondence under the selected convention. | .04–.05, linear functionals, representation proof. |
| U04.5.08 | Existence/decomposition | Real self-adjoint/symmetric and complex self-adjoint/normal spectral theorems with the correct orthogonal/unitary diagonalization conclusions. State the exact scalar field and operator class. | .07, eigenvalue existence and finite-dimensional compactness or another proved source route. |
| U04.5.09 | Existence/decomposition | SVD for an actual rectangular real/complex map or matrix, with nonnegative singular values and correct zero/rank-deficient cases; prove the decomposition rather than assuming its factors. | .06–.08 and positive operators, existence/proof. |
| U04.5.10 | Use requirement | Concrete Gram–Schmidt/projection, a rank-deficient least-squares example, a spectral example and a rectangular SVD, including zero-dimensional boundaries where applicable. | .05–.09, use/controls. |

**Intended tracers.** For the subspace spanned by (1,0) in R², the best fit to
(1,1) is uniquely (1,0). If a two-column matrix has both columns (1,0), all
coefficient pairs with x+y=1 give that same fit: coefficient uniqueness fails.
The native complex convention must yield <(i,0),(1,0)>=-i and
<(1,0),(i,0)>=i. These are planned mathematical checks, not fresh runs.

**False boundaries.** Dependent Gram–Schmidt input cannot be normalized as an
independent basis. A real normal rotation matrix need not be real-diagonalizable;
complex normal and real symmetric conclusions must remain distinct. The exact
eigenvalue/compactness proof spine is still to be selected and audited before
.08 is implemented. Real and complex public interfaces/names remain uncommitted;
do not implement type/arity overloading to choose different contracts.

## U10.1 — Complex limits and differentiability

**Current anchors.** The [complex arithmetic reference](../docs/Manual.md)
already includes this representation and modulus identity:

```litex
z = re(z) + img(z) * i
C_abs(z) = sqrt(re(z)^2 + img(z)^2)
```

This supplies useful arithmetic, not a holomorphic-function theory. The
reserved `lim(a)` and `fn_lim(f,x0)` retain their real sequence/real unary
contracts. No complex overload is proposed. The source-level mathematical
relation must be designed before any new selector name is chosen.

| Requirement | Semantic role | Mathematical contract | Direct dependencies |
| --- | --- | --- | --- |
| U10.1.01 | Domain/bridge | Open subsets D of C, their real-plane representation and actual complete functions D->C. Empty D is allowed; a point interface requires z0 in D. | Complex arithmetic, Euclidean topology, signature/definition. |
| U10.1.02 | Relation/theorem | Complex epsilon-delta limit using C_abs and the actual domain; prove uniqueness at the relevant accumulation points. An isolated point cannot justify a unique selected limit from a vacuous condition. | .01, modulus estimates, definition/uniqueness. |
| U10.1.03 | Relation/results | Complex continuity, algebra, composition and the real/imaginary component bridges. Use exact restrictions and nonzero denominator guards. | .02, real-plane components, proof. |
| U10.1.04 | Relation then guarded value | Derivative candidate L is the limit of (f(z)-f(z0))/(z-z0) over the open domain. Prove uniqueness and existence guards before selecting a derivative value. | .01–.02, division WD, uniqueness/selection. |
| U10.1.05 | Theorem | Sum, scalar, product, quotient and chain rules for actual differentiable functions and compatible domains. | .03–.04, limit algebra, proof. |
| U10.1.06 | Theorem | At an interior point, complex differentiability yields the necessary real partial derivatives and Cauchy–Riemann equations u_x=v_y and u_y=-v_x. | .04, real-plane coordinate paths, proof. |
| U10.1.07 | Theorem | Real total differentiability plus Cauchy–Riemann implies complex differentiability. Continuous first partials in a neighborhood are a sufficient corollary, not part of the definition of complex differentiability. | .04/.06, real total differential and remainder estimate, proof. |
| U10.1.08 | Relation/results | Holomorphic on an open set means differentiable at every point there. Do not identify this with a proved power-series representation until U10.3 supplies that theorem. | .04–.07, definition. |
| U10.1.09 | Theorem | Zero derivative on a connected open domain implies constancy; on disconnected domains use the componentwise conclusion. | .05–.08, real MVT and the needed open-connected/path bridge, proof. |
| U10.1.10 | Use requirement | Differentiate z², reject complex differentiability of conjugation, and test a pointwise-CR counterexample and the derivative/holomorphic distinction. | .04–.09, use/controls. |

**Intended tracer.** Prove the complex derivative of z² is 2*z0 directly from
the difference quotient and use its selected value. For conjugation, real and
imaginary approach directions give different quotient limits, so no derivative
exists on an open neighborhood.

**False boundary.** Define f(0)=0 and, for z=x+i*y!=0,
`f(z)=(x*y/(x²+y²))*z`. All four first partials at 0 vanish and satisfy
Cauchy–Riemann there; the quotient f(z)/z is 0 along the real axis and 1/2 along
x=y. Pointwise partials plus CR are therefore insufficient. Also, z mapped
to its squared modulus has derivative 0 at 0 but is not holomorphic near 0.
These are mathematical controls; no parser/verifier defect is inferred.

## U11.1 — First-order ordinary differential equations

**Current anchors.** The existing
[ODE showcase](../showcases/math_concepts_in_litex/12_ordinary_differential_equations_in_nutshell/main.lit)
contains explicit functions:

```litex
have fn ode_rhs(x, y R) R = 2 * x
have fn quadratic_solution(c, x R) R = x^2 + c
have fn ode_solution(x R) R = x^2 + 1
```

It proves a concrete equation/initial-value family and has its own derivative
relation/selection. For std, audit and reuse the current native real-derivative
interfaces instead of copying a parallel derivative stack. The example is a
proof seed, not general first-order existence or a completed ODE chapter.

| Requirement | Semantic role | Mathematical contract | Direct dependencies |
| --- | --- | --- | --- |
| U11.1.01 | Data/functions | Actual time intervals I, state regions J and RHS F on the intended subset of R×R; an initial point (t0,y0) belongs to that domain. Work on open I for two-sided derivatives, or explicitly specify endpoint one-sided behavior. | Real intervals, functions and domains, signature/definition. |
| U11.1.02 | Relation | A solution y:I->R has values in the admissible state region, the required native derivative, y'=F(t,y), and the initial condition when supplied. The relation does not itself construct a solution. | .01 and native derivative, definition. |
| U11.1.03 | Actual construction/theorem | For continuous g, construct a solution of y'=g(t) by an oriented integral from t0 and prove its derivative/initial value. Do not take the desired antiderivative as an existence premise. | .02, Riemann integrability and FTC in U02.4, construction/proof. |
| U11.1.04 | Actual construction/theorem | For continuous p,q on I, construct the integrating factor mu(t)=exp(integral from t0 to t of p) and the solution of y'+p*y=q. Prove mu>0, correctness and uniqueness on I. | .03, exp/chain/product rules and derivative-zero constancy, existence/WD/proof. |
| U11.1.05 | Method/construction | For y'=g(t)*h(y), separate only where h!=0. Preserve equilibrium solutions at zeros of h. Establish local inversion/range conditions before turning an implicit integral relation into an actual solution. | .03, IVT/monotonic inverse/chain rule, existence/proof. |
| U11.1.06 | Method/theorem | Bernoulli and homogeneous substitutions with their real-power/state and t!=0 domains. Handle exceptional exponents and zero solutions separately rather than dividing them away. | .04–.05, transformation equivalence and WD. |
| U11.1.07 | Actual construction/theorem | For exact M dt+N dy=0, verify a potential and, under the appropriate rectangular/star-shaped C1 hypotheses, construct it from cross-partial equality. A level curve is locally a solution graph only with the needed implicit-function condition. | U03 derivative/FTC facts, potential existence and graph construction. |
| U11.1.08 | Theorem/dependency | Prove the uniqueness promised by each method under its actual assumptions. The general local Lipschitz/Picard theorem remains U11.4; continuity of F alone does not supply it. | .02–.07, MVT/estimates; U11.4 where invoked. |
| U11.1.09 | Use requirement | Construct a linear-IVP solution, a separable solution including equilibria, and a solution whose maximal interval excludes a finite blow-up. | .04–.08, actual values/domains, use. |
| U11.1.10 | Use/boundary requirement | Relate the existing quadratic example to the native-based solution interface; test lost equilibria, zero divisors, invalid powers and nonunique continuous-RHS equations. | .01–.09, source audit/controls. |

**Intended tracers.** Construct y(t)=1-exp(-2*t) for y'+2*y=2,y(0)=0 and prove
uniqueness on R. For y'=y²,y(0)=1, the solution 1/(1-t) has the initial-value
interval (-infinity,1); the formula is not a solution on all R. Separation must
also retain y=0 when solving y'=y² without that nonzero initial condition.

**False boundary.** A continuous RHS can have multiple solutions through the
same initial point. For y'=sqrt(abs(y)),y(0)=0, both the zero function and the
function equal to 0 for t<=0 and t²/4 for t>0 are solutions. Do not infer local
uniqueness without the relevant extra hypotheses. Cross-partial equality on a
domain with holes also does not automatically give a global potential.

**Build order.** Native derivative audit -> solution relation -> .03 FTC
construction -> .04 linear IVP -> .05/.06 transformations -> .07 exact forms.
Track the U02/U03 existence prerequisites instead of weakening these results
to statements about a supplied solution. No general kernel ODE rule is needed
or authorized by this specification.

## U15.1 — Sampling models and sample-statistic laws

**Current anchors.** [Finite probability](probability/main.lit) already has
actual finite spaces, moments and two-event independence. The existing relation
is an event relation:

```litex
prop independent_events(Omega set, space &FiniteProbabilitySpace<Omega>, A, B power_set(space.carrier)):
    space.prob(intersect(A,B)) = space.prob(A)*space.prob(B)
```

It must not be renamed into joint independence of an arbitrary sample family.
The [pushforward interface](probability/README.md) can transport a constructed
sample statistic's distribution. The current exports do not yet construct a
general iid product sample. Continuous sampling also requires the measure and
probability foundations retained in U13/U14; a finite-only demonstration does
not close this chapter.

| Requirement | Semantic role | Mathematical contract | Direct dependencies |
| --- | --- | --- | --- |
| U15.1.01 | Data/structure | A population law or parameterized family on its actual sample space, with explicit parameter domain and normalization. Keep probability-zero outcomes allowed. | Existing finite probability first; later U13/U14 measurable probability, signature/law. |
| U15.1.02 | Actual construction use | Instantiate the n-fold product law/sample space from U14.1.07 with the population law; later use the appropriate U13 measure product. Normalization and product-event formulas are established at their probability owner. The empty product may exist although a mean at n=0 does not. | .01, U14.1.07 and later product measures, construction/use. |
| U15.1.03 | Relations/results | Use U14.1.08 to establish the coordinate sample's common law and joint independence. Preserve the distinction between event, pairwise and whole-family independence rather than adding a second probability interface. | .02 and U14.1.04–U14.1.08, proof/use. |
| U15.1.04 | Function | Sample mean is an actual random variable, and its evaluation is the observed estimate. Require n>=1 for division; distinguish a function of the random sample from its realized numerical value. | .02–.03, finite sum and WD. |
| U15.1.05 | Theorem | The mean of the sample mean equals the common expectation under the required integrability; independence is unnecessary for this linearity result. | .04 and expectation linearity, proof. |
| U15.1.06 | Theorem | First derive the variance formula including covariances; then obtain sigma²/n under common variance and zero pairwise covariances, in particular iid. Include sigma=0. | .04, second moments and current covariance algebra, proof. |
| U15.1.07 | Functions/results | Specify the n-denominator empirical variance and the (n-1)-denominator unbiased sample variance as different operations. The latter needs n>=2; prove its expectation under the actual sampling assumptions. | .04–.06, finite algebra and WD/proof. |
| U15.1.08 | Actual functions/distribution results | Empirical CDF, order statistics with ties preserved, and distribution formulas for extrema/order statistics under the appropriate iid/continuity assumptions. Do not assume a sorting or quantile selector without its construction/domain. | .02–.03, finite order/counting; continuous laws where needed, construction/proof. |
| U15.1.09 | Use requirement | A constructed finite Bernoulli sample, distribution of its count/mean, exact expectation/variance and endpoint parameters 0/1. | .01–.08, binomial counting and pushforward, use. |
| U15.1.10 | Extension requirement | General measurable sample models and standard continuous sample-statistic laws. Cross-map WLLN/CLT to U14.4 and confidence/testing procedures to U15.2–U15.4; keep their existence/normalization prerequisites visible. | U13/U14, product measures and distributional results, proof/import. |

**Intended tracer.** Construct two independent fair Bernoulli observations on
the actual four-outcome product space. Their mean has values 0,1/2,1 with
masses 1/4,1/2,1/4, expectation 1/2 and variance 1/8. Construct the law and
statistic; do not just verify a supplied table that assumes the desired masses.

**False boundaries.** If both observations are the same fair Bernoulli variable,
each marginal is unchanged but the mean has variance 1/4, not 1/8. Pairwise
independent variables need not be jointly independent. Reject a mean at n=0,
an n-1 variance at n=1, and division by sigma in a standardized statistic when
sigma=0. A zero-variance statistic is not required to be pointwise constant at
probability-zero outcomes. These are mathematical controls, not fresh tests.

## S04.1 — Incidence and elementary Euclidean constructions

**Current anchor.** The existing
[coordinate definitions](../showcases/2D_Geometry/geo_definitions.lit) use actual
line/circle point sets. Their directed-segment parallel relation is:

```litex
prop is_parallel(a, b, c, d cart(R, R)):
    a != b
    c != d
    det2(vec(a, b), vec(c, d)) = 0
```

This relation includes coincident supporting lines. Strict parallelism of two
distinct disjoint lines needs a separate fixed contract; extracting the above
must preserve its meaning. The existing midpoint relation permits coincident
endpoints, while the segment-incidence relation has distinct endpoints. The
chapter specification must retain these differences explicitly.

| Requirement | Semantic role | Mathematical contract | Direct dependencies |
| --- | --- | --- | --- |
| S04.1.01 | Reused values/functions | Real-plane points, displacement, dot product, determinant and squared distance, with coordinate formulas. Reuse the established model and prove any bridge to cart_n(R,2). | Existing coordinate definitions and real arithmetic, signature/definition. |
| S04.1.02 | Actual sets/relations | A line from nonzero normal coefficients and the line through distinct points; prove equivalence, membership and uniqueness of the supporting line. Coefficient triples describing the same line need not be equal. | .01, nonzero/collinearity facts, definition/proof. |
| S04.1.03 | Actual sets/relations | Segments, rays and betweenness with explicit parameter domains. Distinguish a possibly degenerate affine segment from an interface that requires two distinct endpoints. | .01–.02, real order, definition/proof. |
| S04.1.04 | Actual sets/relations | Circle with center and positive radius, incidence and squared-distance characterization. A radius-zero point set is not silently admitted as the same nondegenerate-circle operation. | .01, positive radius, signature/definition. |
| S04.1.05 | Classification/construction | Two lines have a unique intersection, are distinct parallel lines, or coincide. Construct the unique point in the nonzero-determinant case and prove both incidence and uniqueness. | .02, Cramer-type scalar identities and denominator WD, existence/proof. |
| S04.1.06 | Classification/construction | Line/circle and circle/circle intersections with feasibility hypotheses, tangency and empty/two-point cases. Supply actual point values when existence is promised. | .01/.04, S02.2 and nonnegative square roots, WD/existence. |
| S04.1.07 | Actual constructions | Midpoint, perpendicular foot to a genuine line and perpendicular bisector of a nonzero segment, with incidence/uniqueness. A midpoint value may remain total when the endpoints coincide. | .01–.05, positive squared direction length, existence/WD. |
| S04.1.08 | Relations/results | Direction parallelism, strict line parallelism and perpendicularity, including the appropriate unique line through a point. Keep their mathematical meanings and public names distinct. | .02/.05/.07, determinant/dot identities, proof. |
| S04.1.09 | Construction objects/results | A finite ruler/compass construction trace and explicit equilateral/perpendicular constructions, each step justified on its actual inputs. A coordinate formula alone does not certify a ruler/compass trace. | .04–.07 and the existing Euclid I.1 construction, construction/proof. |
| S04.1.10 | Use requirement | Intersection, midpoint/bisector and equilateral examples, plus coincident/parallel/tangent and invalid-input controls. Angle-bisector consequences share S04.2 rather than duplicating its interface. | .05–.09, use/controls. |

**Intended tracer.** On A=(0,0),B=(2,0), construct midpoint (1,0), perpendicular
bisector x=1 and the two equilateral vertices (1,±sqrt(3)). For lines x+y=2
and x-y=0, construct their unique intersection (1,1).

**False boundaries.** The equations x+y=2 and 2*x+2*y=4 describe the same line;
they are direction-parallel but not two distinct parallel lines. Repeated
points do not determine a unique supporting line. A claimed circle intersection
must fail when its feasibility conditions are false. These are planned
mathematical controls, not new source verification.

## U02.3 — Mean values, Taylor and derivative applications

**Current anchor.** [Unary higher derivatives](real_multivariable/unary_higher_order.lit)
already separate candidates, existence, actual domains and selected values.
Inside that export the selected expression has this form:

```litex
\nth_derivative<D,k>(f,p)
```

It is guarded by the existing derivative-existence interface; it is not an
unconditional value on every function. Native derivative algebra and
[regularity](real_regularity/README.md) are reusable dependencies. A full
MVT/Taylor chapter still needs its source theorem and application audit.

| Requirement | Semantic role | Mathematical contract | Direct dependencies |
| --- | --- | --- | --- |
| U02.3.01 | Reused relations/functions | Native first derivatives and existing source higher-derivative profiles/values on their actual domains; order zero is evaluation. Prove required restrictions and lower-order availability before selection. | Existing derivative and regularity interfaces, reuse/WD. |
| U02.3.02 | Theorem | Fermat's stationary-point theorem for a differentiable function at an interior local extremum. Endpoint extrema do not carry the same zero-derivative conclusion. | .01, local order/limit proof. |
| U02.3.03 | Existence theorem | Rolle: a<b, continuity on [a,b], differentiability on (a,b) and equal endpoint values yield an interior derivative zero. | U02.2 extrema and .02, existence/proof. |
| U02.3.04 | Existence theorem | Lagrange MVT and Cauchy MVT. Preserve the cross-multiplied Cauchy conclusion without unnecessary nonzero hypotheses; add/prove the needed guards only for a quotient formulation. | .03 and derivative algebra, proof/WD. |
| U02.3.05 | Theorem/applications | Derivative-zero constancy, derivative-sign monotonicity and interval Lipschitz estimates from a derivative bound. Strictly increasing does not imply positive derivative at every point. | .04, interval containment and real order, proof. |
| U02.3.06 | Actual function | Taylor polynomial from the existing order-0 through order-n derivative values at the center, with natural n and proved coefficient domains. Do not construct a second unrelated higher-derivative selector. | .01, factorial and finite sums, definition/WD. |
| U02.3.07 | Existence/error theorem | Taylor's Lagrange remainder, with continuity through order n on the closed segment and the required next derivative in its interior. State a=b or x=center separately; no strict intermediate point exists in a singleton segment. | .03–.06, repeated mean-value argument, proof. |
| U02.3.08 | Theorem/error use | Remainder bounds from an actual nonnegative bound M, plus the mapped local/Peano variants with their own hypotheses. Infinite Taylor equality requires remainder convergence and remains U02.5. | .07, estimates and local limits, proof. |
| U02.3.09 | Theorem/method | Individually specified L'Hopital 0/0 and infinity/infinity variants, with the relevant one-sided/infinite approach, derivative-denominator and limit assumptions. Derive the legitimate quotient limit, not a rule for arbitrary ratios. | .04, exact real-limit relations and denominator WD, proof. |
| U02.3.10 | Use requirement | A secant-slope witness, a monotonicity/extremum application and a Taylor numerical error bound, with failed regularity and invalid L'Hopital cases. | .04–.09, use/controls. |

**Intended tracers.** For t² on [0,2], exhibit the MVT point c=1. Derive
`abs(sin(x)-x)<=abs(x)^3/6` on [-1,1] using the degree-two Taylor polynomial
and a bound on the third derivative. These are planned mathematical results.

**False boundaries.** abs(t) on [-1,1] has equal endpoint values but no interior
derivative zero, because it is not differentiable at 0. The strictly increasing
function t³ has derivative 0 at 0. Derivative quotient 1 for (x+1)/x near 0
does not justify a ratio limit of 1. Smoothness alone does not prove equality
to a Taylor series: the standard exp(-1/x²), extended by 0 at 0, is a later
counterexample obligation, not an assumed analytic function.

## U02.4 — Riemann integration and the fundamental theorems

**Current anchors.** Native [Riemann laws](../src/execute/execute_by_stmt/builtin_thm/riemann_integrals.rs)
already include integrability, values, orientation, Newton–Leibniz and parts;
[substitution](../src/execute/execute_by_stmt/builtin_thm/calculus_substitution.rs)
is also native. The existing four-argument call shape is:

```litex
release thm riemann_integral_newton_leibniz(f,F,a,b)
```

That rule requires a supplied primitive F continuous on the closed interval,
its derivative equal to f on the interior, and integrability of f. It does not
construct a primitive for an arbitrary continuous f. The
[source absolute-integral bounds](real_integral_laws/README.md) are further
reusable results. Audit these precise contracts before adding source wrappers.

| Requirement | Semantic role | Mathematical contract | Direct dependencies |
| --- | --- | --- | --- |
| U02.4.01 | Reused relations/values | Native proper Riemann integral candidates, integrability, unique value and exact complete domains covering the sorted endpoint interval; preserve signed orientation. | Existing native Riemann interfaces, reuse/WD. |
| U02.4.02 | Objects/results | Partitions, tags, sums and the source-facing Riemann criterion. Connect textbook definitions to the native relation rather than defining a parallel integral with unproved equivalence. | .01, finite sequences/sums and interval partitions, definition/proof. |
| U02.4.03 | Theorem | Continuous functions on closed bounded intervals are integrable; inventory native support. Add the mapped step/piecewise and integrability criteria with their exact assumptions. | U02.2 and .01–.02, reuse/proof. |
| U02.4.04 | Actual function | For integrable f on [a,b], construct the accumulation function F(x)=integral from a to x of f on that actual interval. Prove each selected integral's existence and F's continuity. | .01–.03, subinterval integrability, bounds and WD/existence. |
| U02.4.05 | Theorem | FTC I: at an interior continuity point of f, the derivative of .04 is f(x). For continuous f, obtain an actual primitive on the interval interior and, when a<b, the correct one-sided endpoint conclusions. | .04, local integral estimates and native derivatives, proof. |
| U02.4.06 | Theorem/transport | FTC II/Newton–Leibniz with integrable f and a valid primitive, retaining endpoint continuity and interior differentiation. Reuse the native rule where its contract matches; no new kernel theorem is proposed. | .01/.05 and existing native rule, reuse/proof. |
| U02.4.07 | Methods/results | Substitution, parts and elementary antiderivatives, with correct function/range/orientation and denominator domains. Translate the textbook methods onto existing native interfaces. | .05–.06, derivative rules and existing substitution/parts, proof/WD. |
| U02.4.08 | Results/applications | Integral monotonicity, absolute/error bounds, signed area, elementary geometric applications and representative calculations. Additional curve/volume constructions remain explicit dependencies. | .01–.07 and existing source bounds, proof/use. |
| U02.4.09 | Relations then guarded values | Ordinary improper integrals as appropriate one-sided/infinite limits, including interior singularities and separate tail convergence. Establish uniqueness and convergence before selecting a value; principal value is a distinct operation. | .01 and exact limit relations; comparisons/series where used, definition/proof. |
| U02.4.10 | Use requirement | Construct an accumulation primitive, calculate oriented/degenerate integrals and establish a convergent/divergent improper pair with valid error/domain reasoning. | .04–.09, use/controls. |

**Intended tracers.** For f(t)=t² on [0,1], construct F(x)=x³/3 from the
accumulation integral and prove F'=f, not merely the reverse calculation from
a supplied F. Check reversal and equal endpoints. Later compare the integrals
of 1/t² and 1/t on [1,infinity).

**False boundaries.** The integrable step f(t)=0 for t<0 and 1 for t>=0 on
[-1,1] has accumulation function max(x,0), which is not differentiable at 0.
Integrability alone does not give FTC I at every point. Cancellation across
the singularity of 1/t on [-1,1] does not give an ordinary improper integral,
even though its symmetric principal value is 0.

## U04.2 — Matrix representations, systems and determinants

**Current anchors.** [Coordinate maps](algebra/coordinate_maps.lit) already use
actual basis-coordinate values of this form:

```litex
\basis::basis_coordinates<K,field,V,space,n,vectors>(x)
```

They prove reconstruction and linearity over a supplied field. The existing
[matrix package](matrix/main.lit) uses native R/C operations, for example:

```litex
template<m,n N>:
    have fn column_vector(mat matrix(C,m,n),c closed_range(1,n)) cart_n(C,m)=fn(r closed_range(1,m)) C {mat(r,c)}
```

The general representation chapter must retain the arbitrary-field scope of
the coordinate layer. Native R/C operators may be connected by proved concrete
bridges; their presence is not evidence for an unexamined arbitrary-field
matrix-arithmetic contract.

| Requirement | Semantic role | Mathematical contract | Direct dependencies |
| --- | --- | --- | --- |
| U04.2.01 | Actual value family | Finite m-by-n coefficient arrays over a supplied field, including zero dimensions, with entrywise equality. Preserve the actual complete row/column index domains and supplied field operations. | Existing field and finite-function interfaces, signature/definition. |
| U04.2.02 | Actual operations/results | Matrix addition, scalar action, product and identity over that field, with dimensions and field laws explicit. Prove native R/C correspondence separately rather than retyping arbitrary field elements as numbers. | .01, finite coefficient sums and field algebra, definition/proof. |
| U04.2.03 | Actual construction | Given ordered source/target bases and linear T, construct A whose (i,j) entry is the ith target coordinate of T(source_basis(j)). Prove coordinate(Tx)=A*coordinate(x). | Existing coordinate maps, .01–.02, construction/proof. |
| U04.2.04 | Theorem/construction | Matrices and linear maps correspond for the chosen bases; identities, sums and composition correspond with the correct multiplication order. Construct the map represented by a supplied matrix. | .03 and existing extension from basis, existence/uniqueness. |
| U04.2.05 | Actual construction/theorem | Change-of-basis matrices and inverse coordinate transport. If P,Q send new source/target coordinates to old coordinates, A_new=Q^(-1)*A_old*P. Endomorphisms use P^(-1)*A*P. | .03–.04 and invertible basis maps, proof/WD. |
| U04.2.06 | Actual algorithm/results | Elementary row operations and Gaussian/RREF construction over a field, with legal nonzero pivots and termination. Rectangular/rank-deficient arrays remain allowed; a pivot must be constructed when promised. | .01–.02, finite ordered search and elimination invariant, existence/proof. |
| U04.2.07 | Classification/construction | Solve Ax=b completely: inconsistency certificate or one actual particular solution plus the kernel. Prove uniqueness exactly under the relevant kernel/injectivity conditions. | .06, existing kernel/image/rank-nullity, proof/construction. |
| U04.2.08 | Function/results | Determinant with its defining finite construction or equivalent multilinear characterization, determinant of the empty matrix equal to field.one, and row-operation/multiplicativity laws. | .01–.02, permutations or multilinear construction, existence/proof. |
| U04.2.09 | Theorem/construction | Square invertibility criteria, inverse construction and Cramer formulas under nonzero determinant; connect the abstract field result to current native determinant/inverse contracts where applicable. | .06–.08, existence/uniqueness/WD. |
| U04.2.10 | Use requirement | A nonstandard-basis representation, composition/change-of-basis calculation, consistent/inconsistent/underdetermined systems and zero-dimensional cases. | .03–.09, use/controls. |

**Intended tracer.** For T(x,y)=(x+y,y) on R² and the ordered basis
((1,0),(1,2)), the coordinate matrix has columns (1,0),(2,1), hence rows
((1,2),(0,1)). Verify it by actual coordinate reconstruction and change of basis;
this choice distinguishes the correct conjugation order from its reversal.
For the duplicated-row matrix with rows (1,1),(1,1), RHS (1,1) gives the
affine family x+y=1, while RHS (1,2) is inconsistent.

**False boundaries.** A basis change is not generally P*A*P^(-1) under the
stated convention. An invertible square solver does not solve an arbitrary
rectangular or singular system. Empty matrices and zero spaces must not acquire
an artificial positive-dimension hypothesis merely to fit native operations.

## U05.3 — Formal polynomials and polynomial division

**Current anchors.** [Unital rings](algebra/ring.lit) already expose operations
and a separate commutativity property; the source explicitly allows the zero
ring. The current data fields are:

```litex
struct Ring<K nonempty_set>:
    zero K
    one K
    add fn(x,y K) K
    neg fn(x K) K
    mul fn(x,y K) K
```

This excerpt omits the existing laws; it is not a proposed replacement struct.
The chapter needs an actual polynomial construction above those interfaces.
Candidate representation: coefficient functions N->K with proved finite support.
Finite lists modulo trailing zeros are another possibility to resolve before
implementation. Evaluation as a function on K is not the polynomial's identity.

| Requirement | Semantic role | Mathematical contract | Direct dependencies |
| --- | --- | --- | --- |
| U05.3.01 | Actual carrier/constructors | Formal finite-support coefficient data over an existing commutative unital ring; zero, constants and indeterminate are actual values. Preserve the zero ring and explain coefficientwise equality. | Existing Ring and commutativity relation, finite-support construction. |
| U05.3.02 | Actual operations/results | Coefficientwise sum/negation and convolution product, with support bounds and the polynomial-ring laws proved from coefficient operations. | .01 and finite sums, definition/proof. |
| U05.3.03 | Actual function/theorem | Evaluation and its ring-homomorphism/substitution property, with the coefficient map and target assumptions explicit. Equality of evaluations on a finite field is not coefficient equality. | .01–.02, finite powers and ring homomorphisms, proof. |
| U05.3.04 | Relation then guarded value | Degree, leading coefficient and support bounds. The source uses degree(0)=-infinity; a natural-valued nonzero-only degree plus an all-polynomial support-bound relation is a candidate interface, not a silent source equivalence. | .01, finite support, maximum existence and uniqueness. |
| U05.3.05 | Theorem | Degree of a nonzero product is the sum over an integral domain; use weaker support/degree bounds over rings with zero divisors. Keep zero cases meaningful without evaluating a guarded degree at zero. | .02/.04 and exact coefficient-ring assumptions, proof/WD. |
| U05.3.06 | Actual algorithm/theorem | Over a field, divide by a nonzero polynomial and construct unique quotient/remainder, with remainder zero or strictly smaller degree. A monic/unit-leading variant over a ring needs its own stated contract. | .02/.04, inverse leading coefficient, degree descent, existence/WD. |
| U05.3.07 | Results/constructions | Remainder/factor theorem, roots and multiplicities, and root-count bound for a nonzero polynomial over an integral domain/field. A root set alone does not provide factorization. | .03/.05–.06, division and nonzero factors, proof. |
| U05.3.08 | Actual construction/theorem | Euclidean algorithm, polynomial Bezout and a uniquely normalized monic gcd when at least one operand is nonzero. One zero operand remains allowed. | .06, termination and coefficient normalization, existence/uniqueness. |
| U05.3.09 | Theorem/extension | Irreducibility, principal ideals and unique factorization in F[X]; content/primitive-polynomial and Gauss-lemma extensions over a UFD are separately mapped to Judson 18.2. | .05–.08 and ring/ideal/UFD interfaces, proof. |
| U05.3.10 | Use requirement | Polynomial division, factor/root and gcd/Bezout examples, plus finite-field function-equality and zero-divisor controls. | .01–.09, use/controls. |

**Intended tracers.** Over Q, divide X³-1 by X-1, obtaining quotient X²+X+1
and zero remainder, then verify the actual coefficient identity. Over F2,
X²-X is nonzero as a polynomial although evaluation is zero at every field
element. Over Z/4Z, the nonzero polynomial 2*X has square zero, preventing
an unconditional nonzero-product degree formula.

**Decision boundary.** Representation and the zero-degree convention need a
source-facing design decision before public declarations. The model must not
identify formal polynomials with functions to avoid that decision. All proposed
operations stay in source; no parser/AST polynomial node is authorized.

## U07.1 — Subsets, permutations and binomial counting

**Current anchors.** [Combinatorics](combinatorics/main.lit) already has native
cardinality interfaces and numeric binomial laws, including this source header:

```litex
thm binomial_factorial_formula:
    ? forall n,k N:
        k<=n
        =>:
            binomial_coefficient(n,k)=factorial(n)/(factorial(k)*factorial(n-k))
```

That formula and the actual complex binomial expansion are not yet the
cardinality proof for k-element subsets. The existing total powerset count,
finite-map bounds and fiber sums are usable dependencies to audit. Keep the
paused extension's incomplete imported/refusal acceptance visible.

| Requirement | Semantic role | Mathematical contract | Direct dependencies |
| --- | --- | --- | --- |
| U07.1.01 | Actual finite sets/results | Finite words/functions, disjoint choices and Cartesian choices, with addition/product counting justified on actual carriers. Include empty choice families. | Existing finite cardinality, functions and product sets, construction/proof. |
| U07.1.02 | Actual set-valued function | The set of k-element subsets of finite X, as a genuine subset of power_set(X), for every natural k. Its construction and finiteness precede cardinality goals. | Finite powerset/subset closure and cardinality, definition/WD. |
| U07.1.03 | Theorem/domain cases | At k=0 the family is {empty set}; if k>size(X) it is empty. In particular, empty X has one zero-element subset and no positive-size subsets. | .02 and finite-set bounds, proof. |
| U07.1.04 | Actual bijections/results | Partition k-subsets by membership of a chosen point; construct removal/adjoining inverse maps. Handle k=0 separately before using k-1. | .01–.03, set difference/union and disjoint counting, construction/proof. |
| U07.1.05 | Cardinality theorem | Count the actual family in .02 as binomial_coefficient(size(X),k) for all natural k, by a proved recurrence or a genuine counting bijection. | .03–.04 and existing numeric Pascal laws, proof. |
| U07.1.06 | Actual sets/counting theorem | Ordered samples without repetition and permutations have falling-factorial/factorial counts; words with repetition have size(X)^k. Define above-size/empty cases without a negative factorial. | .01/.05, finite maps and recursion, construction/proof. |
| U07.1.07 | Theorem/bridge | Relate ordered and unordered selections by a proved k!-fiber map and transfer numeric factorial/binomial formulas to the actual counted sets. | .05–.06 and finite uniform-fiber counting, proof. |
| U07.1.08 | Actual sets/results | Ordered partitions with prescribed block sizes and multinomial counts. Supply the disjoint-cover family and its nonnegative integer count before a factorial-quotient interpretation. | .05–.07, finite families and sum constraints, construction/proof. |
| U07.1.09 | Actual sets/results | Repeated-choice multisets/weak compositions and stars-and-bars bijections, with the number-of-boxes zero case separated before formulas containing k-1. | .02/.05/.08, finite sequence encoding and bijection, proof. |
| U07.1.10 | Use requirement | Concrete subset/permutation and repeated-choice counts, plus empty, oversized and ordered-versus-unordered controls. | .03–.09, use/controls. |

**Intended tracers.** For a five-element X, construct its two-element-subset
family and prove its cardinality 10. The actual two-position injective sequences
have cardinality 20, and the forgetting-order map has fibers of size 2. Use
the zero-element-subset family on empty X as a separate boundary case.

**False boundaries.** The zero-element-subset family is not empty. Using n!
instead of a falling factorial for partial selections, treating sequences as
subsets, or dividing by k! without proving uniform fibers does not establish
the desired counting theorem. No count predicate may take the target binomial
formula as an input assumption.

## U14.1 — Discrete laws and joint independence

**Current anchors.** [Finite probability](probability/main.lit) has two-event
independence, actual pushforward laws, finite moments and zero-mass outcomes.
The existing pushforward family is an actual construction:

```litex
template<Omega set,space &FiniteProbabilitySpace<Omega>,Target set,F fn(k space.carrier) Target>:
    have fn finite_pushforward_event_probability(A power_set(fn_range(F))) R=space.prob(preimage_set(F,A))
```

Target may be infinite while fn_range(F) is finite; that does not construct a
countably supported probability law. Joint independence and product-space
construction belong here and are reused by U15.1 sampling, not recreated there.

| Requirement | Semantic role | Mathematical contract | Direct dependencies |
| --- | --- | --- | --- |
| U14.1.01 | Reused data/constructions | Actual finite probability laws with event probabilities and singleton masses, including zero-mass points and arbitrary ambient target sets. Distinguish image/range from positive-mass support. | Current FiniteProbabilitySpace and constructors, reuse. |
| U14.1.02 | Functions/results | Discrete random variables and actual PMF/CDF or set-valued pushforward laws; derive normalization and event probabilities from preimages. | .01 and current pushforward, finite/countable sums as appropriate. |
| U14.1.03 | Actual maps/distributions | Joint finite tuples of random variables and their joint law, with marginals obtained by projection and summation. The actual coordinate map precedes its law. | .02, tuple/function domains and marginalization, construction/proof. |
| U14.1.04 | Relations/results | Independence of variables/families via joint event factorization; distinguish it from pairwise independence and from the existing relation on two events. Include the empty and one-variable family conventions. | .01–.03, event preimages and finite products, definition/proof. |
| U14.1.05 | Equivalence theorems | For discrete laws, joint independence is equivalent to the appropriate joint-PMF product formula; prove subfamily and transformed-variable consequences. Do not substitute a product of marginal masses without this proof. | .02–.04, finite/countable summation and event partitions, proof. |
| U14.1.06 | Functions/results | Conditional discrete laws on positive-probability conditioning events/atoms, with total-probability/Bayes and independence consequences. Independence itself remains meaningful when some masses are zero. | .02–.05 and existing guarded event conditioning, WD/proof. |
| U14.1.07 | Actual construction | Finite products of supplied finite probability spaces, including the unit empty product; prove nonnegativity, normalization and product-event probabilities from the constructed law. | .01, finite Cartesian products/sums and cardinality, construction/proof. |
| U14.1.08 | Theorem/owned bridge | Product coordinates have the supplied marginal laws and are jointly independent. Reuse this object and theorem for iid sampling and Bernoulli count laws; common marginals are an additional condition, not independence itself. | .03–.05/.07, proof; U15.1 use. |
| U14.1.09 | Construction/results | Countably supported laws with countable additivity, normalized PMFs, joint/marginal laws and the discrete expectation/independence results with justified sums. A geometric law on N+ is a required infinite-support construction. | Real nonnegative series, countable event sums and reindexing/additivity proofs; U13 bridges where used. |
| U14.1.10 | Use requirement | Construct independent coordinates and a pairwise-but-not-jointly-independent family, verify endpoint probabilities/conditioning guards, and distinguish the finite result from the remaining countable extension. | .01–.09, use/controls. |

**Intended tracers.** On the uniform four-point bit-pair space, let X,Y be the
coordinate bits and Z their exclusive-or. Every pair is independent, but
P(X=0,Y=0,Z=0)=1/4 differs from the product 1/8. The same constructed product
space supplies the independent two-observation sample in U15.1. Later build
the infinite-support law p(n)=2^(-n),n>=1 with its actual event measure.

**False boundaries.** Pairwise factorization does not imply joint factorization.
A zero-probability conditional atom does not license division by its mass.
Normalization of a proposed infinite PMF alone does not prove the required
countable-additivity/event-law construction. An infinite ambient type with a
finite actual carrier remains a finite probability space.

## U03.2 — Total differentiation and local inverse constructions

**Current anchors.** The [multivariable example](../examples/real_analysis/multivariable/main.lit)
already distinguishes scalar and vector differential interfaces, including:

```litex
scalar_differential(bowl,(1,2),2)(1,1)=2
differential(field,(1,2,3),3,3)(2,2)=1
```

These are existing excerpts, not new overloads. Native total-derivative and
chain-rule contracts are in [multivariable.rs](../src/execute/execute_by_stmt/builtin_thm/multivariable.rs).
The source [regularity layer](real_regularity/README.md) supplies scalar C^k
interfaces. Audit the componentwise vector-C1 bridge before using it in an
inverse theorem. Existing partials/Jacobian candidates do not by themselves
establish the full remainder estimate for total differentiability.

| Requirement | Semantic role | Mathematical contract | Direct dependencies |
| --- | --- | --- | --- |
| U03.2.01 | Reused relations/values | Native scalar/full-vector derivative candidates, existence, uniqueness and selected values on actual real domains. Retain distinct scalar/vector names and exact dimensions, rather than introducing an overloaded differential contract. | Current native differential interfaces, reuse/WD. |
| U03.2.02 | Actual linear maps/bridges | Finite-dimensional linear maps and their matrix/norm estimates, with the relation between a derivative map and its coordinate matrix proved. | U04.2, finite real norm bounds, definition/proof. |
| U03.2.03 | Theorems | Total differentiability implies continuity and the corresponding directional/partial candidates. Establish the correct Jacobian/gradient bridge; partial existence alone is not the converse theorem. | .01–.02 and coordinate paths, proof. |
| U03.2.04 | Reused laws/theorems | Derivative linearity, products where meaningful and composition, with actual range/domain containment and correct matrix multiplication order. Audit native support before adding source theorem wrappers. | .01–.03 and native chain rules, reuse/proof. |
| U03.2.05 | Relations/theorem | Componentwise continuous first partials imply total differentiability and a continuous derivative map on an open domain. Reuse scalar regularity and construct the vector-C1 interface needed by later results. | .01–.04, local estimates and current C^k definitions, proof. |
| U03.2.06 | Local existence theorem | A C1 map U->R^n with invertible derivative at p has actual open neighborhoods V,W and an inverse g:W->V of its restriction. Produce V,W,g existentially; no canonical neighborhoods are assumed. | .02/.05, complete closed real-coordinate balls and a contraction/existence proof. |
| U03.2.07 | Theorems/guarded inverse | Prove differentiability of that local inverse and Dg=(Df)^(-1) at corresponding points, then the mapped C^k variants. A selected inverse is unique after its restricted domains/map are fixed. | .04/.06, matrix inverse guards and regularity, uniqueness/proof. |
| U03.2.08 | Local existence theorem | For F(x,y)=0 with invertible y-block derivative, construct neighborhoods and an actual local solution function h, with the exact local zero-set equivalence and uniqueness. | .05–.07, explicit product/coordinate identifications, existence/proof. |
| U03.2.09 | Theorem/application | Dh=-(D_y F)^(-1)D_x F and the corresponding implicit parametrization uses, preserving matrix shapes and neighborhood conditions. | .04/.08, block derivatives and nonzero inverse guards, proof. |
| U03.2.10 | Use requirement | Actual local inverse/implicit functions and derivative values, plus partial-only and local-versus-global counterexamples. Initial calculus profiles use the current positive-dimension convention; zero-dimensional algebraic compatibility remains an explicit separate audit. | .03–.09, use/controls. |

**Intended tracers.** Near (0,0), invert (x,y) mapped to (x,y+x²) using the
actual inverse (u,v) mapped to (u,v-u²). Near (x,y)=(0,1), solve x²+y²=1 as
y=sqrt(1-x²) on explicit neighborhoods and derive its derivative.

**False boundaries.** For f(x,y)=x³/(x²+y²), extended by 0 at the origin, all
directional derivatives there exist but their values depend nonlinearly on
the direction; no total derivative follows. The map
(x,y) mapped to (exp(x)*cos(y),exp(x)*sin(y)) has nonzero Jacobian determinant
everywhere and is not globally injective. Do not publish a global inverse from
the local theorem.

**Existence dependencies.** A Banach-based proof must construct the real-coordinate
metric, prove completeness of the relevant closed ball and establish the
self-map/contraction estimates. [metric_sequences](metric_sequences/README.md)
supplies the general fixed-point theorem; it does not supply those inputs merely
by import. Finite-coordinate norm estimates can precede spectral theory, avoiding
an unnecessary spectral-theorem dependency cycle.

## U05.1 — Groups, actions, cosets and quotients

**Current anchors.** [Group source](algebra/group.lit) already has the actual
group data, subgroup/homomorphism relations and a kernel construction. Its
normal-subgroup relation includes conjugation closure:

```litex
prop is_normal_subgroup(A nonempty_set, G &Group<A>, S power_set(A)):
    $is_subgroup(A, G, S)
    forall a A, s S:
        G.mul(G.mul(a, s), G.inv(a)) $in S
```

Reuse those laws, cancellation, inverses and image/kernel results. Existing
[equivalence classes](relations/main.lit) provide another construction to audit
for cosets; do not add a parallel relation/class mechanism just for groups.

| Requirement | Semantic role | Mathematical contract | Direct dependencies |
| --- | --- | --- | --- |
| U05.1.01 | Reused structures/results | Current Group, subgroup, homomorphism, image, kernel and normality interfaces; construct inherited subgroup structures and cyclic subgroups where needed. A group is inhabited by its identity, including the trivial group. | Existing group/field source, reuse/construction. |
| U05.1.02 | Actual constructions | Product groups, element powers/orders and basic cyclic/permutation examples, with actual operations and proved group membership. A supplied multiplication table alone is not a group construction proof. | .01, finite recursion and permutations, construction/proof. |
| U05.1.03 | Actual sets/theorems | Left/right cosets and their equivalence/partition laws for an actual subgroup; translation gives a genuine bijection between subgroup and coset. | .01, existing equivalence-class infrastructure, construction/proof. |
| U05.1.04 | Actual construction | Quotient group by a normal subgroup, with a well-defined multiplication/inverse and actual quotient projection. Define the output without choosing arbitrary representatives. | .03, normality and unique well-defined class products, existence/proof. |
| U05.1.05 | Counting theorem | Finite Lagrange/index and element-order divisibility, proving the actual uniform-coset fibers and their finiteness. | .02–.03, U07 counting and source fiber laws, proof/WD. |
| U05.1.06 | Actual maps/theorems | First, second and third isomorphism results with the constructed induced maps and exact images/quotient domains. Surjectivity onto an image is not surjectivity onto an arbitrary ambient codomain. | .01/.04, kernel/image and map factorization, existence/proof. |
| U05.1.07 | Structure/constructions | Group actions on actual sets, including the empty action carrier; actual orbits and stabilizer subgroups, plus the coset-to-orbit bijection for a supplied point. | .01–.03, function actions and set constructions, definition/proof. |
| U05.1.08 | Theorems | Orbit–stabilizer, class equation and Cauchy's theorem with the right finite hypotheses. A stabilizer need not be normal. | .05/.07, finite counting and conjugation action, proof. |
| U05.1.09 | Existence/counting theorems | Sylow subgroup existence, conjugacy and subgroup-count conditions. Construct the subgroup witnesses; an assumed p-subgroup does not prove the existence theorem. | .05/.07–.08 and finite number theory, existence/proof. |
| U05.1.10 | Use requirement | Actual cyclic/quotient and noncommutative action examples, a nonnormal-subgroup boundary and trivial-group/empty-action cases. | .02–.09, use/controls. |

**Intended tracers.** Construct Z/6Z and its reduction onto Z/3Z, identify the
kernel and construct the induced quotient isomorphism. On the action of S3 on
three letters, exhibit an orbit of size 3 and a stabilizer of size 2, giving
the count 6=3*2.

**False boundaries.** That point stabilizer in S3 is not normal, so its coset
set is not automatically a quotient group. A map with the correct kernel but
an unjustified surjectivity claim cannot yield the claimed codomain isomorphism.
Coset construction/proofs must retain the distinction between left and right
cosets before normality is available.

## U08.1 — Paths, connectivity, trees and degree counting

**Current anchor.** [FiniteSimpleGraph](graph_theory/main.lit) stores ordered
arcs and explicitly enforces symmetry:

```litex
arcs power_set(cart(Vertices,Vertices))
```

The complete structure also excludes loops and fixes its actual vertex carrier.
The source already defines neighbors/degrees and complete/complement/induced
graphs. Each undirected edge gives two arcs; no new edge count may silently
identify the two cardinalities. All constructions must preserve the fixed-carrier
contract or explicitly use an induced graph with its new carrier.

**Checked counting increment.** [graph_theory](graph_theory/README.md) now
constructs the actual unordered-edge image and proves its two-vertex and
two-arc properties. The 34-theorem / 60-statement strict source, 147 imported
statements, independent examples of 5 and 11 statements, and 28 final-only
refusals pass. The original 36 source and 96 caller statements are exact
preserved prefixes. Levin 4.1.5 and the 4.1.7 application are mapped here;
4.1.8 odd-degree subset parity still requires a separate construction/proof.

| Requirement | Semantic role | Mathematical contract | Direct dependencies  Current evidence |
| --- | --- | --- | ---  --- |
| U08.1.01 | Actual set/function | The unordered-edge set consists of actual two-element vertex subsets whose endpoints are adjacent. Prove finiteness and its two-to-one correspondence with ordered arcs. | Current graph data, native powerset closure and U07 finite-fiber counting, construction/proof. General binomial subset counting is not needed by this construction.  Checked: actual `graph_edges`, finiteness, distinct endpoints, edge cardinality 2 and the two-arc fiber theorem. |
| U08.1.02 | Actual data/relations | Finite walks, endpoints and length; a length-zero walk still contains its one vertex. Simple paths have the specified no-repetition condition; simple cycles in this loop-free undirected model have length at least three, with the specified distinct-vertex and closing-edge conditions. | Finite vertex sequences, adjacency and natural indices, definition/WD.  Planned. |
| U08.1.03 | Constructions/theorems | Concatenation/reversal and removal of repeated sections; connected endpoints admit a simple path with an appropriate finite length bound. | .02, finite recursion and loop removal, construction/proof.  Planned. |
| U08.1.04 | Relations/actual sets | Reachability equivalence, connected components and connectedness conventions. Propose nonempty connected graphs and explicitly nonempty trees, while forests and the component set allow the empty graph; audit textbook conventions before public naming. | .02–.03 and equivalence partitions, definition/proof.  Planned. |
| U08.1.05 | Theorem | Handshaking: sum of degrees equals twice the unordered-edge cardinality; separately prove the sum equals the arc cardinality. Include empty/singleton graphs. | .01, finite incidence/fiber sums and existing degree definition, proof.  Checked: `graph_degree_sum_equals_arc_count`, `graph_arc_count_twice_edge_count` and `graph_handshake`, including empty/singleton callers. |
| U08.1.06 | Theorem | The number of odd-degree vertices is even, with an actual finite vertex subset and parity proof. | .05 and finite parity/counting, proof.  Planned: actual odd-degree subset and parity proof. The native `$dvd` follow-up does not establish this item. |
| U08.1.07 | Relations/equivalence theorems | For a finite nonempty graph, tree, unique paths, and the appropriate connected/acyclic plus n-1 edge criteria agree. Keep an explicit vertex in the singleton case and do not apply n-1 blindly to n=0. | .02–.05, cycle/path arguments and counting, proof.  Planned. |
| U08.1.08 | Existence/constructions | Every finite connected graph has an actual spanning tree on the same vertex set. A canonical algorithm needs explicit ordered search data; mere existence does not supply a unique selected tree. | .03/.07, finite edge selection and invariants, existence/proof.  Planned. |
| U08.1.09 | Theorems/constructions | Leaves in nontrivial finite trees, leaf deletion/pruning, and the forest identity edges=vertices-components, including the empty forest. | .04/.07–.08, finite induction, proof.  Planned. |
| U08.1.10 | Use requirement | A three-vertex path and triangle with separately checked arc/edge counts, a spanning tree witness and empty/singleton/loop controls. | .01–.09, use/controls.  Partial: path arc/edge counts 4/2, triangle edge count 3 and degree sum 6, empty/singleton/invalid-loop controls. Spanning-tree and tree/cycle statements are not supplied. |

**Intended tracer.** The three-vertex path has degrees 1,2,1, four ordered arcs
and two unordered edges. Prove 1+2+1=2*2 and that its two edges form a tree.
The triangle has six arcs and three edges and is not a tree. The counting
portion now has the evidence above; tree/spanning-tree claims remain planned.

**False boundaries.** Counting arcs as edges doubles the wrong side of the
handshaking statement. The empty forest has zero components and edges but is
not a nonempty tree. A closed walk with repeated vertices is not automatically
a simple cycle, and a disconnected graph need not have a spanning tree.

## U09.2 — Bases, product spaces and quotient spaces

**Current anchors.** [TopologicalSpace](topology/main.lit) already bundles
actual carriers and open families:

```litex
struct TopologicalSpace<Ambient set>:
    carrier power_set(Ambient)
    opens power_set(power_set(carrier))
```

The excerpt omits its existing direct laws. Subspace construction and exact
restricted-map values are already supplied; they are reused, not replaced.
Products and quotient topology must likewise be actual topological-space values
with the needed laws, rather than predicates on a proposed result.

| Requirement | Semantic role | Mathematical contract | Direct dependencies |
| --- | --- | --- | --- |
| U09.2.01 | Reused constructions | Current discrete/indiscrete/subspace spaces, restrictions and continuity/homeomorphism interfaces, including empty carriers and ambient/actual-carrier distinctions. | Existing topology source, reuse. |
| U09.2.02 | Relations then constructors | Basis/subbasis conditions, the actual generated open family and least-topology/mapping characterizations. A family of rectangles alone is generally only a basis, not the whole topology. | .01, arbitrary unions and finite intersections, definition/existence/proof. |
| U09.2.03 | Actual construction/theorem | Binary and finite product spaces on actual Cartesian carriers, with projections continuous and the coordinatewise continuity characterization. | .02, Cartesian products and preimages, construction/proof. |
| U09.2.04 | Actual construction/theorem | Indexed products with finite-support basic cylinders and the universal mapping property; include the empty-index unit space and possibly empty products. Do not derive inhabitedness from inhabited factors without the relevant principle. | .02–.03, indexed function/set carriers, construction/proof. |
| U09.2.05 | Constructions/results | Disjoint-union/sum spaces and the distinction between product and box topologies for infinite families; prove the stated mapping properties with exact carriers. | .02–.04, tagged unions and preimages, construction/proof. |
| U09.2.06 | Actual construction | Quotient carrier of actual equivalence classes, its projection and quotient open-family definition; prove the projection onto that carrier is surjective. | Current relations classes/partitions and topology, construction/proof. |
| U09.2.07 | Actual induced map/theorem | A continuous map constant on the projection's fibers factors uniquely through the quotient and has the appropriate continuity equivalence. Use unique fiber values, not a global representative selector. | .06, well-definedness and unique factorization, existence/proof. |
| U09.2.08 | Theorems | Open or closed continuous surjections give the appropriate quotient-map conclusion; retain surjectivity and do not equate every continuous surjection with a quotient map. | .01/.06–.07 and existing closed-map facts, proof. |
| U09.2.09 | Compatibility results | Source-specific subspace/product/sum/quotient comparisons and homeomorphisms, with restrictions stated precisely. A quotient's arbitrary restriction or product is not automatically a quotient map. | .03–.08, explicit preimage/canonical-map arguments, proof. |
| U09.2.10 | Use requirement | Construct finite products, a nontrivial quotient and an induced map; check empty/unit cases and a continuous-surjection counterexample. | .01–.09, use/controls. |

**Intended tracer.** Quotient the discrete three-point space by the partition
{{0,1},{2}}, construct its two-point quotient space and factor a map taking
one value on {0,1} and another on {2}. All classes, projection and induced-map
values must be supplied by the construction.

**False boundaries.** The identity from a discrete two-point space to the
indiscrete space is continuous and surjective, but the target does not carry
the quotient topology of that identity. Arbitrary unions of basic rectangles
are required for product opens; the single rectangles alone are not closed
under unions. Full choice/Tychonoff claims remain separately audited principles.

## U13.1 — Sigma-algebras, measures and outer measure

**Current anchor.** The finite probability structure has the real-valued field:

```litex
prob fn(E power_set(carrier)) R
```

It is a valid finite foundation. General measures also take the value infinity,
so a source-level extended-value construction and its exact operations/order are
needed before the general chapter. This is a mathematical interface requirement,
not authorization for a native infinity/AST change. The value representation
must also accommodate the shared extended-value needs of convex analysis.

| Requirement | Semantic role | Mathematical contract | Direct dependencies |
| --- | --- | --- | --- |
| U13.1.01 | Structures/actual families | Sigma-algebra on an actual carrier, measurable sets, generated sigma-algebras and the Borel sigma-algebra. Empty carriers are allowed. Closure is countable, not only finite. | Existing set/function operations, countable unions, definition/construction. |
| U13.1.02 | Actual value family/operations | Extended nonnegative values with infinity, order and nonnegative countable sums; align with a common extended-real design where needed. Do not use an unguarded finite real supremum or undefined infinity subtraction. | Real completeness and nonnegative series, construction/WD. |
| U13.1.03 | Structure | Measure on its measurable-set domain with empty value zero and countable disjoint additivity, including infinite total mass. Finite/probability and sigma-finite are separate properties. | .01–.02, direct laws. |
| U13.1.04 | Theorems | Monotonicity, subadditivity, continuity from below and continuity from above with its finite-measure hypothesis. State finite-difference formulas only under the needed finiteness conditions. | .03, countable sums and disjointification, proof. |
| U13.1.05 | Actual construction | Outer measure from admissible countable covers and a premeasure/length assignment, with the infimum and cover-existence conventions established. Its domain is all subsets, its additivity is not assumed. | .01–.02, cover families and extended infima, construction/proof. |
| U13.1.06 | Actual family/theorem | Caratheodory measurable-set criterion gives a sigma-algebra and a complete measure by restriction. Use the splitting equality, not subtraction of two infinite values. | .04–.05, countable subadditivity and restriction, construction/proof. |
| U13.1.07 | Extension theorem | Premeasure extension on the generated sigma-algebra, with the source's semiring/algebra hypotheses and sigma-finiteness when uniqueness is claimed. Existence and uniqueness are separate obligations. | .01/.05–.06 and the supplementary extension source, existence/uniqueness. |
| U13.1.08 | Actual construction/theorems | Lebesgue measure from interval lengths, Borel restriction and completion; prove interval values and measurable/null-set consequences without declaring every subset of R measurable. | .05–.07, real intervals and length/countable-cover proofs. |
| U13.1.09 | Examples/bridges | Counting and Dirac measures; embed existing finite probability as a finite discrete measure. A reverse finite-probability bridge needs all subsets measurable, not merely a finite underlying set. | .01–.03/.08, current probability source and exact embeddings, construction/proof. |
| U13.1.10 | Use requirement | Infinite counting measure, Lebesgue interval/null-set examples and a continuity-from-above counterexample with infinite initial mass. | .04–.09, use/controls. |

**Intended tracers.** Counting measure on N has singleton values 1 and total
mass infinity. Lebesgue measure gives [0,1] value 1 and each singleton value 0.
The finite discrete bridge must recover the existing actual probability values,
including zero-mass outcomes.

**False boundaries.** For A_n=[n,infinity), each Lebesgue measure is infinity
but the intersection is empty; continuity from above cannot omit its finite-mass
hypothesis. Sigma-additivity does not mean additivity over arbitrary uncountable
families. A finite-carrier sigma-algebra may omit some subsets, so it cannot
automatically be retyped as the existing full-powerset probability structure.

**Representation boundary.** The extended-value encoding, countable sums and
general premeasure extension remain substantial source work. The selected
Axler and Norris foundations are references, not evidence that these objects
already exist in std. No countably supported construction is marked complete
by supplying only a normalized sequence of finite real masses.

## U16.4 — Interpolation, approximation and quadrature

**Current anchor.** [Numerical analysis](numerical_analysis/main.lit) currently
constructs a square-root Newton update:

```litex
have fn newton_sqrt_step(a,x R+) R+ = (x+a/x)/2
```

Its convergence/error proofs and the general contraction module are reusable
tools, not interpolation/quadrature results. This chapter also consumes the
formal polynomial carrier of U05.3, real integration in U02.4 and the relevant
higher derivatives. Hermite/Gaussian extensions need their exact supplementary
textbook-section mapping before chapter acceptance.

| Requirement | Semantic role | Mathematical contract | Direct dependencies |
| --- | --- | --- | --- |
| U16.4.01 | Actual data/constructor | Distinct real interpolation nodes and supplied values; construct the unique polynomial of degree at most N-1 for N>=1. Separate an empty-data problem before making a uniqueness claim. | U05.3 coefficient identity, division/evaluation and nonzero node differences. |
| U16.4.02 | Actual formulas/results | Lagrange/Newton forms, divided differences and barycentric evaluation; prove they produce the same interpolant. At a node return its supplied value rather than evaluate a zero denominator. | .01, finite products and polynomial identities, construction/WD. |
| U16.4.03 | Error theorem | Interpolation remainder and derivative-based bounds on a region containing both nodes and evaluation point, with actual smoothness assumptions and exact node cases. | .01–.02, U02.3 repeated Rolle/Taylor, proof. |
| U16.4.04 | Actual constructions/results | Piecewise-linear interpolation and cubic splines with specified natural/clamped or other boundary data. Prove the corresponding existence/uniqueness; continuity and interpolation alone do not uniquely specify a cubic spline. | .01–.03, U04.2 systems and knot ordering, construction/proof. |
| U16.4.05 | Approximation results | Approximation norms, node-dependent error/stability estimates and mapped polynomial/Chebyshev approximation results. A zero nodal error does not imply a zero uniform error. | .03–.04, function bounds and source-specific approximation theorems. |
| U16.4.06 | Actual function | A quadrature functional from actual nodes/weights and evaluations, with domain coverage; derive its polynomial-exactness conditions. Do not take a promised quadrature error estimate as input data. | U02.4 integrals, .01–.02 and finite sums, definition/proof. |
| U16.4.07 | Actual formulas/error theorems | Midpoint, trapezoid, Simpson and composite formulas with smoothness, interval, mesh and Simpson parity requirements. Prove absolute truncation-error bounds. | .03/.06, derivative/integral estimates, proof/WD. |
| U16.4.08 | Construction/theorem | Mapped Gaussian quadrature and weighted extensions: construct nodes/weights, prove exactness and positivity under their proper assumptions. Supplied candidate weights alone do not establish existence. | U04.5 orthogonality/spectral or polynomial-root route, .06 and integration. |
| U16.4.09 | Algorithm/error result | Adaptive subdivision and stopping/error guarantees under stated computable bounds or proven estimators. Comparing two numerical outputs is not itself a rigorous error certificate. | .07 and finite recursion/estimate invariants, proof. |
| U16.4.10 | Use requirement | Construct an interpolant and a quadrature value with a numerical error bound; include repeated-node, missing-boundary-data and insufficient-smoothness controls. Rounding/stability claims separately use U16.1. | .01–.09, use/controls. |

**Intended tracers.** Interpolate t² at -1 and 1 to obtain the actual polynomial
p=1, and quantify its error at 0. For integration of t² on [0,1], the trapezoid
value is 1/2 with error 1/6, and midpoint value is 1/4 with error 1/12. Prove
the corresponding derivative bounds and compare to the integral 1/3.

**False boundaries.** Repeated nodes invalidate the ordinary distinct-node
Lagrange denominators. Interpolating at all supplied nodes does not make a
nonpolynomial function equal to the interpolant everywhere. A cubic spline
without its boundary conditions is not generally unique; exact-real error
proofs do not establish a floating-point implementation's stability.

## U17.1 — Convexity, separation and foundational optimality

**Current anchors.** Real vectors, norms and derivatives are available through
[real_multivariable](real_multivariable/README.md). The existing example uses
both a gradient candidate and total differentiability:

```litex
$has_gradient_at(bowl,(1,2),2,(2,4))
$is_multi_differentiable_at(bowl,(1,2),2)
```

Use the exact total-differentiability guard for derivative-based convexity or
stationarity statements. The current inner-product projection tools are still
planned in U04.5. Extended-valued convex functions share a value-design need
with U13.1 but are not restricted to nonnegative finite values.

| Requirement | Semantic role | Mathematical contract | Direct dependencies |
| --- | --- | --- | --- |
| U17.1.01 | Relations/actual sets | Convex/affine sets, convex hulls, cones and finite convex combinations on actual real vector carriers. Empty convex sets are allowed; existence theorems state their separate nonemptiness requirements. | Existing real coordinates and finite combinations, definition/construction. |
| U17.1.02 | Relations/actual sets | Convex functions on actual convex domains, epigraphs, strict/strong convexity and basic closure/composition rules with their monotonicity/domain assumptions. | .01, real-valued functions and epigraph construction, definition/proof. |
| U17.1.03 | Relations/constructions | Proper extended-valued convex functions, domain/indicator extension and lower semicontinuity, using the shared extended-real design. Do not silently overload finite real arithmetic with infinity cases. | .01–.02 and U13.1 extended-value foundation, definition/WD. |
| U17.1.04 | Theorems | First-order supporting inequality for differentiable convex functions on an open convex domain; C2 Hessian-positive-semidefinite characterization on its proper domain. Partial candidates alone do not provide the derivative hypothesis. | .02, U03.2/U03.3 derivative bridges and U04.5 form positivity, proof. |
| U17.1.05 | Actual construction/theorem | Euclidean projection onto a nonempty closed convex subset, with existence and uniqueness even for unbounded sets. Build the minimizing point using finite-dimensional compactness/coercive bounds, not completeness alone. | .01, Euclidean norm and compactness/strict-convexity proof. |
| U17.1.06 | Existence theorems | Supporting/separating hyperplanes with the distinct open/closed/compact hypotheses required for weak or strict separation. Construct a nonzero separating normal and valid bounds. | .01/.05 and geometric estimates, existence/proof. |
| U17.1.07 | Existence/uniqueness results | Continuous objectives on nonempty compact feasible sets attain minima; the corresponding closed/coercive variants retain their conditions. Strict convexity gives at most one minimizer, not existence by itself. | .01–.02, U02/U09 compactness and coercive-sublevel arguments. |
| U17.1.08 | Optimality theorems | For differentiable convex f on an open domain containing convex C, characterize a feasible minimum by grad f(p) dot (x-p)>=0 for all x in C. The unconstrained stationary corollary has its own interior/domain hypotheses. | .04/.07 and directional arguments, proof. |
| U17.1.09 | Relations/results | Subgradients and subdifferential sets, zero-subgradient optimality and finite Jensen inequalities. State the domain/relative-interior conditions for existence or identification with a gradient. | .01–.04, supporting inequalities and finite convex sums, definition/proof. |
| U17.1.10 | Use requirement | A constructed constrained minimizer, a projection/separation example and strict-convexity/existence counterexamples. KKT, duality and descent algorithms remain U17.2–U17.5. | .05–.09, use/controls. |

**Intended tracer.** Minimize (x+1)² on C=[0,infinity). Construct the unique
minimizer x=0 and prove optimality although the ambient derivative there is 2.
The constrained inequality is the correct criterion; a zero gradient is not
necessary at the boundary. Project (2,0) onto the closed unit disk and exhibit
the corresponding separating hyperplane.

**False boundaries.** exp(x) is strictly convex on R and does not attain its
infimum. A stationary point of a nonconvex objective need not minimize it.
The disjoint closed convex sets {(x,y):y>=exp(x)} and {(x,y):y<=0} have distance
zero, so closedness alone does not give a positive uniform separation margin.
Infinite-dimensional completeness alone does not supply
the finite-dimensional compactness argument used by the projection proof.

## Shared construction ownership

| Construction | Mathematical owner | Reuse obligations |
| --- | --- | --- |
| Midpoint, foot, perpendicular bisector | S04.1.07 | S04.2 applies the actual values to triangles and proves median/bisector consequences; no second geometric operation is needed. |
| Existing higher-derivative values and profiles | Current real_multivariable/real_regularity exports | U02.3 consumes them for Taylor; U10/U11 use the appropriate existing real differential interfaces. |
| Basis coordinates and map from basis values | Current algebra coordinate_maps/basis/finite_span exports | U04.2 adds matrix representation and systems; U04.5 reuses them for adjoints/spectral statements. |
| Finite probability product and its coordinate laws | U14.1.07–U14.1.08 | U15.1 instantiates the actual product with a common population law; the statistical layer does not duplicate probability construction. |
| Formal polynomial carrier and operations | U05.3.01–U05.3.04, after representation decision | U04.3 characteristic polynomials and later quotient/field extensions reuse this carrier; native numeric expressions do not replace it. |
| Real-coordinate metric, completeness and compactness bridges | Metric/metric_sequences/topology source spine, audited through U09 and U03.2 prerequisites | U03.2 inverse/implicit proofs and U17.1 projection/separation consume the actual ball/space results; generic completeness alone does not assert compactness. |
| Equivalence-class carrier and projection | Existing relations source, with each induced equivalence relation proved | U05.1 adds quotient group operations and U09.2 adds quotient topology on actual classes, without arbitrary representative selectors. |
| Unordered graph edges | U08.1.01 using U07.1 two-subset/fiber constructions | Handshaking, tree counts and later graph algorithms reuse the same edge notion and its proved relation to ordered arcs. |
| Extended-value/order foundation | U13.1.02, with a common design for the relevant extended-real carrier | Nonnegative measures/integrals and proper extended-valued convex functions use explicit appropriate subcarriers and guarded operations; no ad hoc native overload is introduced. |
| Linear orthogonal projection and convex nearest points | U04.5.06 and U17.1.05 with their respective fixed contracts | Prove the specialization relation for linear subspaces; do not choose linearity or existence claims by argument type under an ambiguous name. |
| Interpolating polynomial values | U16.4 using the U05.3 polynomial carrier | Lagrange/Newton/barycentric forms and quadrature share the proved coefficient/evaluation bridges rather than separate polynomial identities. |

These ownership edges prevent accidental duplicate interfaces. They do not
commit file names, public names or an additional module dependency. Resolve
representation/naming questions against existing source before implementation.

## Dependency order and handoff

Each row identifies three different kinds of edge; none is a new trust edge.

| Slice | Signature/definition inputs | Proof/existence/WD inputs | Produced downstream use |
| --- | --- | --- | --- |
| S02.2 | Real numbers, exact finite formulas and sets | Real order, principal roots, nonzero denominators | Elementary solving, conic intersections and parameter cases. |
| S04.2 | Real-plane coordinates, nondegenerate triangles and incidence | Scalar identities, positive lengths, congruence bridges and actual point constructions | School geometry, analytic geometry and geometric applications. |
| U02.2 | Actual interval functions and native continuity | Completeness/suprema or a proved compactness bridge | Extrema, IVT, uniform continuity; later MVT, FTC and approximation. |
| U04.5 | Existing spaces/bases and an explicit real/complex inner product | Residual positivity, finite-dimensional representation and spectral existence inputs | Least squares, quadratic forms, numerical linear algebra and operator theory. |
| U10.1 | Open complex domains, C_abs and actual functions | Complex-limit uniqueness, real differential estimates, connected-domain bridge | Holomorphic maps, later analytic/integral theory. |
| U11.1 | Native real derivatives and actual time/state domains | U02 FTC/MVT, inverse/implicit-function or method-specific existence results | Constructed IVPs and later stability/numerical methods. |
| U15.1 | Actual probability laws, sample products and statistic functions | Counting, joint independence, covariance algebra; measure/product construction for the continuous extension | Sampling distributions, estimation, tests and regression. |
| S04.1 | Real-plane point sets, circles, segments and rays | Nonzero directions, scalar solving and square-root feasibility | Actual basic constructions consumed by S04.2 and analytic geometry. |
| U02.3 | Current native/source derivative interfaces and finite Taylor functions | Interval extrema, Rolle/MVT and exact higher-derivative hypotheses | Quantified approximation, monotonicity, FTC/ODE uniqueness prerequisites. |
| U02.4 | Native Riemann relations/values and actual accumulation functions | Integrability, subinterval guards, local estimates and FTC | Constructed primitives, ODE solutions and numerical/integral applications. |
| U04.2 | Existing arbitrary-field basis coordinates and finite arrays | Field operations, elimination, determinant/inverse existence | Matrix representations, complete system solving and later spectral theory. |
| U05.3 | Existing commutative-ring/field data and formal finite coefficients | Support/degree proofs, division descent and factorization hypotheses | Characteristic polynomials, polynomial quotients and field extensions. |
| U07.1 | Actual subset/sequence/partition families | Numeric binomial laws, finite bijections and uniform fibers | Sampling laws, combinatorial identities and finite algorithm counts. |
| U14.1 | Current finite probability and actual product/joint laws | Finite event sums and independence proofs; countable additivity for infinite support | Shared sampling product, discrete distributions and later stochastic theory. |
| U03.2 | Exact scalar/vector differential interfaces and real coordinate maps | Local remainder estimates, matrix bounds and complete-ball/contraction proofs | Actual local inverses and implicit parametrizations on specified neighborhoods. |
| U05.1 | Existing groups, subgroups, homomorphisms and equivalence classes | Normality, well-defined class operations, finite coset/action counts | Quotient groups, induced isomorphisms, actions and Sylow witnesses. |
| U08.1 | Fixed-carrier finite simple graphs, unordered edges and finite walks | Arc/edge bridge, path/cycle arguments and finite induction | Handshaking, actual spanning trees and forest counts. |
| U09.2 | Existing topology/relations and generated carrier/open families | Basis laws, preimage arguments and unique fiber-value factorization | Actual product/sum/quotient spaces and their mapping properties. |
| U13.1 | Sigma-algebras, extended values and actual cover families | Countable sums, outer-measure proofs and extension/uniqueness hypotheses | General measures, Lebesgue construction and finite-probability bridges. |
| U16.4 | Formal polynomial values, nodes/weights and actual integrals | Interpolation uniqueness, derivative error bounds and quadrature existence | Approximation/splines/quadrature with stated guarantees. |
| U17.1 | Real convex sets/functions and derivative/extended-value interfaces | Finite-dimensional compactness, projection, separation and supporting inequalities | Constructed minimizers and correct constrained/unconstrained optimality. |

First finish the reusable arithmetic/geometry extraction and the interval
existence spine; advance finite-product probability and finite inner-product
construction as their independent prerequisites permit. Split spectral,
continuous-sampling and exact-ODE work at their honest dependencies. Do not
drop the harder portions when an early finite/example slice passes.

Before implementation, turn each row into a precise statement/interface card,
check public names, choose the smallest coherent source-owned location and
audit the source edition. Follow persistent Session proof work and clean
source/import/false-boundary verification when that work starts. The present
increment creates only durable Markdown planning artifacts and retains the
previous cleanup. All mathematical implementation requirements remain open.
