# Mathematical Design: Single-Variable Real Calculus

## Implemented first-version slice

`main.lit` now checks the real derivative-candidate relation, the derivative
of `x^2`, a parameterized affine derivative theorem, differentiability as
candidate existence, and the exact quadratic error from the tangent to `x^2`
at `3`. It contains no direct `trust` and does not select a derivative before
uniqueness is proved.

## Core interface cards

### Sequence limit candidate

- **Meaning:** the terms of a real sequence eventually lie within every
  positive epsilon of a supplied real value `L`.
- **Form:** `prop has_sequence_limit(a, L)` built from an explicit tail-control
  relation.
- **Sketch:** `forall epsilon R+: exist n0 N+ st {forall n N+: n>=n0 =>
  abs(a(n)-L)<epsilon}`.
- **Rejected form:** an unconditional `limit(a)` function; existence and
  uniqueness have not yet supplied a canonical value.
- **Dependencies:** positive reals, absolute value, sequence carrier, and
  natural-number tails.
- **Use:** convergence, uniqueness, algebra of limits, and continuity.

### Function limit candidate

- **Meaning:** function values approach `L` as inputs in a supplied real subset
  approach `x0` through a punctured neighborhood.
- **Form:** `prop has_function_limit(E,f,x0,L)`.
- **Rejected form:** globalizing every function to `R -> R` or silently
  evaluating outside `E`.
- **Dependencies:** real subsets, punctured neighborhoods, absolute distance.
- **Use:** continuity and derivative difference quotients.

### Continuity

- **Meaning:** the function limit at a point equals the function value there.
- **Form:** `prop is_continuous_at(E,f,x0)` and a separate on-set predicate.
- **Rejected form:** a structure in the first tranche; callers assert the
  property but do not yet pass a package with projected data.
- **Use:** composition, extrema, IVT, and continuous integrability.

### Derivative candidate

- **Meaning:** the punctured-domain difference quotient approaches supplied
  value `L` at `x0`.
- **Form:** `prop has_derivative_at(E,f,x0,L)` with a smaller delta-control
  relation.
- **Sketch:** for every positive epsilon, some positive delta controls the
  error of `(f(x)-f(x0))/(x-x0)` whenever `x` is in `E`, `x != x0`, and
  `abs(x-x0)<delta`.
- **Rejected form:** a primitive derivative function with no existence or
  uniqueness boundary.
- **Dependencies:** punctured function limit and a limit-point condition on
  `x0` when the domain is not all of `R`.
- **Use:** differentiability, derivative uniqueness, and derivative rules.

### Selected derivative

- **Meaning:** the unique derivative candidate of a differentiable function at
  a non-isolated point.
- **Form:** `have fn ... by exist!` after derivative existence and uniqueness.
- **Rejected form:** a default derivative at nondifferentiable or isolated
  points.
- **Use:** derivative-sign theorems and familiar calculated notation.

### Riemann partition and sums

- **Meaning:** a finite ordered subdivision of `[a,b]`, optionally with tags,
  and the finite lower/upper/tagged sums it determines.
- **Form:** a `struct` only when projection of points/tags/laws is needed;
  sums are callable functions of verified partition data.
- **Rejected form:** an abstract integral candidate that hides all finite-sum
  and mesh obligations.
- **Dependencies:** finite sequences, strict order, intervals, finite sums,
  extrema on compact subintervals.
- **Use:** integrability and integral algebra.

### Integral candidate and selected integral

- **Meaning:** a supplied number satisfies the Riemann approximation criterion;
  for an integrable function it is unique.
- **Form:** `prop has_riemann_integral(a,b,f,I)`; after existence and uniqueness,
  a selected `have fn integral(a,b,f)`.
- **Rejected form:** postulating a value-returning integral for every function.
- **Use:** linearity, interval additivity, accumulation functions, and FTC.

### Fundamental Theorem of Calculus

- **Meaning:** integration produces an antiderivative under continuity, and an
  antiderivative evaluates the definite integral under the exact hypotheses.
- **Form:** two named `thm` interfaces, not a definition or Builtin rule.
- **Dependencies:** continuous integrability, interval additivity, derivative
  estimates/MVT, and selected derivative/integral interfaces.
- **Use:** accumulated-area example and later applications.

## Main dependency DAG

```text
R, abs, R+, N+
  -> tail-control relation                         [signature, definition]
  -> sequence-limit candidate                      [definition]
  -> convergence                                   [existence]
  -> limit uniqueness                              [proof]
  -> selected sequence limit                       [selection]
  -> limit algebra                                 [proof]

real subsets + punctured neighborhoods
  -> function-limit candidate                      [definition]
  -> continuity                                    [definition]
  -> continuity algebra/composition                [proof]
  -> compact-interval extrema + IVT                 [proof, completeness]

function-limit machinery
  -> difference quotient                           [definition, well_definedness]
  -> derivative candidate                          [definition]
  -> differentiability                             [existence]
  -> derivative uniqueness                         [proof]
  -> selected derivative                           [selection]
  -> derivative rules                              [proof]
  -> Fermat -> Rolle -> MVT                        [proof]
  -> monotonicity/equation uniqueness              [proof]

finite ordered partitions + finite sums
  -> Riemann sums                                  [definition, law]
  -> integral candidate                            [definition]
  -> integrability                                 [existence]
  -> integral uniqueness                           [proof]
  -> selected definite integral                    [selection]
  -> integral laws + continuous integrability      [proof]
  -> accumulation function                         [definition]
  -> FTC I and FTC II                              [proof]
```

## Topological implementation order

1. Candidate sequence limit and constant/`1/n` probes.
2. Sequence-limit uniqueness and selected limit.
3. Function limits and continuity.
4. Compact interval dependencies, EVT, and IVT.
5. Difference quotient and derivative candidate; keep the square tracer live.
6. Derivative uniqueness and selected derivative.
7. Derivative algebra, Fermat, Rolle, MVT, and monotonicity application.
8. Partition and finite-sum interfaces.
9. Integral candidates, uniqueness, and selected integral.
10. Continuous integrability, integral laws, FTC, and accumulated-area
    application.

## Boundaries and unresolved dependencies

- Builtin real arithmetic is a source/trust boundary of the whole project; its
  completeness story must be cited honestly rather than rederived casually.
- Archimedean bounds are required by `1/n -> 0`.
- EVT and IVT require a checked compactness/completeness route.
- MVT must not enter before the extreme-value/Fermat/Rolle chain is checked.
- Riemann integration requires stable finite partition, finite sum, and
  supremum/infimum or equivalent approximation interfaces.
- Existing textbook translations may contain trusted versions of derivative
  uniqueness, MVT, continuous integrability, or FTC. They are evidence and
  mining material, not proof that this scratch spine is checkable.
- No cycle may be broken by defining the selected limit, derivative, or
  integral first and using it to prove its own uniqueness.
