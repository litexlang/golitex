# Finite covariance geometry

Covariance uses the existing centered-product expectation of two total real
functions on one actual finite sample carrier. Its square bound is the finite
Cauchy--Schwarz inequality; it is a theorem, not a new relation or selected value.
The proof considers Var(tX+Y), which is a nonnegative quadratic in every real t.
A private scalar proof handles the zero leading coefficient by contradiction
and the positive coefficient by completing the square at t=-Cov/Var(X).
The public theorem therefore never divides by a possibly zero variance.

The left/right zero-variance consequences follow by bounding the covariance
square by0 and using the real-square zero law, with symmetry for the right side.
The actual Dirac example retains a nonempty null outcome and distinct function
values, so these consequences cannot silently assume everywhere constancy.

The sum and difference formulas cancel their covariance cross terms in the
parallelogram identity. Nonnegativity of the complementary variance gives
each upper bound. This route reuses the already proved source formulas and
requires no square roots, independence or positive variance.

The Bernoulli and affine example attains the square bound and demonstrates
that replacing <= with < is false. Repeating the Bernoulli observable in the
sum similarly shows the factor2 variance bound can be attained. Wrong domains
and missing premises remain separate controls, rather than countermodels.

All values, space laws and sampler domains are imported from std/probability.
Finite-set arithmetic calibrates the examples; no source trust, user axiom,
abstract predicate, native rule or compiler change is added. Correlation,
probability tail inequalities, distributions and measure probability are
separate downstream work.
