# Plan: Single-Variable Real Calculus

## Reader promise

This file should grow one-variable calculus from explicit approximation
relations into usable values and theorems. A reader should see where epsilon,
delta, compactness, and completeness enter rather than encountering a list of
preinstalled derivative and integral formulas.

The project covers the standard conceptual arc from limits through the
Fundamental Theorem of Calculus, but it is divided into independent gates. A
later gate does not become checkable by assuming its flagship theorem merely
to finish the narrative.

## Foundational decision

The first project is calculus of real-valued functions of one real variable.
It uses the Builtin real carrier and explicitly records every additional
completeness, interval, compactness, finite-partition, or finite-sum interface
needed by a theorem.

The project has three release gates:

- **Gate A -- limits and continuity:** real sequences, candidate limits,
  uniqueness, function limits, continuity, and the compact-interval results
  needed later.
- **Gate B -- differentiation:** derivative candidates, uniqueness and
  selection, derivative algebra, Fermat, Rolle, the Mean Value Theorem, and a
  monotonicity/equation-uniqueness application.
- **Gate C -- Riemann integration:** partitions and sums, integrability,
  integral uniqueness and algebra, and both directions of the Fundamental
  Theorem of Calculus on closed intervals.

The currently executable scratch tracer belongs to Gate B but deliberately
uses only its local epsilon-delta derivative relation. It does not claim that
Gate A's general uniqueness/compactness infrastructure or Gate C is complete.

## Mathematical boundary

Included in Gate A:

- real sequences as functions from positive naturals to reals;
- epsilon-tail sequence-limit relation;
- convergence and uniqueness of sequence limits;
- constant-sequence and `1/n -> 0` examples;
- sum, product, scalar, and quotient limit laws with explicit nonzero bounds;
- epsilon-delta function limits on real subsets;
- continuity at a point and on a set;
- continuity under arithmetic and composition;
- sequential characterization only after both directions are checkable; and
- closed-interval boundedness, attainment of extrema, and the Intermediate
  Value Theorem, with completeness/compactness dependencies visible.

Included in Gate B:

- difference quotient on a punctured real domain;
- `has_derivative_at(f, x0, L)` as a candidate-value relation;
- differentiability as existence of such a candidate;
- derivative uniqueness, followed only then by a selected derivative value;
- derivatives of constants, identity, affine functions, and the square;
- sum, scalar, product, reciprocal, quotient, and chain rules;
- differentiability implies continuity;
- local extrema, Fermat's theorem, Rolle's theorem, and the Mean Value Theorem;
- derivative-sign monotonicity; and
- one non-toy application proving monotonicity, an extremum, or uniqueness of
  a solution.

Included in Gate C:

- closed intervals and finite ordered partitions;
- lower/upper sums or an equivalent honest Riemann-sum interface;
- Riemann integrability as equality/control of lower and upper approximations;
- uniqueness of the integral value before selecting an integral function;
- integrals of constant and step functions;
- linearity, order preservation, interval additivity, and an absolute-value
  estimate;
- continuous functions on closed intervals are Riemann integrable;
- the integral accumulation function; and
- FTC I and FTC II with their exact continuity/differentiability hypotheses.

Explicitly excluded:

- multivariable calculus, manifolds, differential forms, vector calculus, and
  differential equations;
- infinite series and power series beyond an optional downstream application;
- uniform convergence as a separate theory;
- measure theory, Lebesgue integration, probability, Fourier analysis, and
  improper integrals;
- complex analysis;
- generalized derivatives, distributions, or numerical analysis;
- treating every differentiable function as globally defined on `R` when the
  theorem is actually local or interval-relative; and
- broad axioms for MVT, continuous integrability, or FTC merely to make later
  examples short.

The stop rule is FTC for continuous functions on a compact real interval plus
one application that consumes it. Anything requiring measure, several
variables, infinite series, or differential equations belongs in another
project.

## Internal architecture

1. **Real approximation language:** absolute distance, positive epsilon and
   delta, tails, punctured domains, and closed intervals.
2. **Candidate relations:** `has_sequence_limit`, `has_function_limit`,
   `has_derivative_at`, and `has_riemann_integral` retain the proposed value as
   an explicit argument.
3. **Existence predicates:** convergence, differentiability, and integrability
   state that a candidate exists.
4. **Uniqueness theorems:** prove candidate values equal under the appropriate
   domain hypotheses.
5. **Canonical selections:** expose `limit`, `derivative`, and `integral` only
   after existence and uniqueness are established on an explicit domain.
6. **Algebra and composition laws:** consume the relations or selected values
   without silently changing carriers.
7. **Compact-interval bridge:** boundedness, extrema, IVT, Rolle, and MVT.
8. **Finite-partition bridge:** partitions, Riemann sums, integrability, and
   interval additivity.
9. **Flagship:** FTC, followed by a concrete accumulated-area or equation-
   uniqueness application.

## Main theorem chain

Gate A:

```text
epsilon-tail closeness
  -> sequence has candidate limit
  -> constant and 1/n examples
  -> uniqueness of sequence limits
  -> selected sequence limit on convergent sequences
  -> limit algebra
  -> epsilon-delta function limit
  -> continuity at a point / on a set
  -> continuity algebra and composition
  -> compact closed intervals
  -> boundedness + extrema + Intermediate Value Theorem
```

Gate B:

```text
punctured-domain difference quotient
  -> derivative candidate relation
  -> square-function epsilon-delta tracer
  -> differentiability
  -> derivative uniqueness
  -> selected derivative
  -> sum/product/quotient/chain rules
  -> differentiability implies continuity
  -> Fermat
  -> Rolle
  -> Mean Value Theorem
  -> derivative sign gives monotonicity
  -> equation uniqueness / extremum application
```

Gate C:

```text
finite ordered partition
  -> lower/upper or tagged Riemann sums
  -> integral candidate relation
  -> integrability
  -> integral uniqueness
  -> selected definite integral
  -> linearity + order + interval additivity
  -> continuous functions are integrable
  -> accumulation function
  -> FTC I
  -> antiderivative evaluation / FTC II
  -> accumulated-area application
```

The three selections must not form definition cycles. Candidate relations and
existence predicates come first; uniqueness is proved independently; only then
may `have fn ... by exist!` expose a callable value.

## Scratch example ladder

1. A constant sequence converges to its constant value -- first epsilon-tail
   witness.
2. `1/n -> 0` -- first example that exposes the Archimedean dependency.
3. A concrete affine function is continuous -- direct epsilon-delta control.
4. `f(x)=x^2` has derivative `2*x0` at every real `x0` -- current tracer;
   the difference quotient becomes `x+x0`, and choosing `delta=epsilon`
   finishes the proof.
5. Product rule applied to `x^2 * (x+1)` -- first reusable derivative-law
   consumer.
6. `f(x)=x^3+x` is strictly increasing, hence `f(x)=c` has at most one real
   solution -- Gate B flagship consumer after MVT.
7. Integrate a constant or step function from its finite partition -- first
   Riemann-sum computation.
8. For `f(x)=2*x`, prove the accumulation function on `[0,b]` is `x^2` and
   evaluate the definite integral by FTC -- Gate C flagship.

Examples 1--3 are foundation probes. Example 4 is the first public tracer.
Examples 6 and 8 are the intended non-toy consumers for Gates B and C.

## Modeling decisions

- a candidate limit, derivative, or integral is a `prop` relation because a
  proof asserts that a supplied value satisfies an approximation condition;
- convergence, differentiability, and integrability are existence predicates,
  not synonyms for the selected value;
- `limit`, `derivative`, and the definite integral are selected functions only
  after unique existence is checkable;
- the difference quotient is a callable function on the punctured domain when
  downstream proofs apply it repeatedly;
- continuity is a property of a supplied function at a supplied point or on a
  supplied set;
- a partition is packaged data only if callers need to project ordered points,
  subintervals, tags, and laws; otherwise start with the weakest verified
  finite interface;
- integral sums are formula-defined functions of a partition/tag choice, while
  integrability is a property; and
- MVT and FTC are ordinary named theorems, never Builtin rules.

## Lean comparison scenes

Use two comparisons, each with identical mathematical assumptions:

1. **First contact:** derivative of `x^2` at `x0`. Show idiomatic Lean with its
   derivative/filter library and the Litex epsilon-delta witness proof. Explain
   that Lean provides a much more general topological derivative framework;
   Litex's example favors a direct school-calculus interface.
2. **Mature core:** the Mean Value Theorem or FTC. Compare dependency surfaces,
   not line counts. Lean's mature analysis library is a major advantage; the
   Litex question is whether the visible fact-oriented chain is easier for
   students and agents to construct and repair.

Record exact imports, versions, and checked source before publishing either
comparison. Do not compare a fully proved Lean theorem with a Litex theorem
whose compactness, MVT, integrability, or FTC step is trusted.

## Acceptance gates

Current tracer:

- independently passes both release file and module runners;
- defines the derivative candidate relation rather than asserting a derivative
  function without uniqueness;
- keeps `x != x0`, the nonzero denominator, epsilon, and delta witness visible;
- has no direct `trust` or local axiom.

Gate A:

- candidate relation, convergence, uniqueness, and selected limit are distinct;
- `1/n -> 0` records the exact Archimedean input;
- function-limit and continuity domains are explicit;
- compactness/completeness dependencies of EVT and IVT are visible and
  checkable; and
- the main spine has no direct `trust`.

Gate B:

- derivative uniqueness is proved before selection;
- algebra and chain rules consume the same derivative relation/interface;
- MVT follows from checked compact-interval results rather than an axiom;
- monotonicity/equation uniqueness consumes MVT; and
- the main spine has no direct `trust`.

Gate C:

- partition order and finiteness are explicit;
- integral uniqueness precedes selected integral notation;
- continuous integrability is proved, not assumed for the flagship;
- FTC hypotheses distinguish continuity from differentiability precisely;
- the final accumulated-area example consumes FTC; and
- the main spine has no direct `trust`.

## Expected downstream consumers

Elementary algebra supplies calculation and inequality patterns. Sets and
functions supply domains, restrictions, images, and preimages. Linear algebra
and calculus later meet in least squares only after an inner-product interface
exists; that cross-domain consumer is deliberately outside this file.
