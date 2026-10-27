# Finite probability consumers

This project consumes std/probability rather than introducing another
probability model. Its actual carriers are the six dice outcomes and the two
points of a Dirac example. All probability-space laws come from the generic
uniform or Dirac constructor; numeric values are checked from those functions.

Events are actual subsets. Their intersection, difference and complementary
partition lead to conditional probabilities, Bayes and total probability.
Conditioning requires positive evidence probability. The Dirac carrier has a
nonempty null event, separating nonemptiness from positive probability and
making the conditioning guard observable.

Real observables are complete functions on the supplied actual carrier.
Expectation is their weighted finite sum. Singleton weights normalize by the
general theorem; means and second moments are then exact arithmetic. Changing
an observable only at a null outcome preserves its mean in the supplied example.
Variance0 does not imply constancy at every point of the carrier.

Covariance is the centered-product expectation. Its product-moment formula
and bilinearity are imported source theorems, not assumptions about the dice.
For X(k)=k and Y(k)=2X(k)+1, the positive covariance35/6 is required in the
variance105/4 of X+Y. Dropping the cross term is the nearest incorrect formula.
The general addition law therefore needs no independence premise, whereas its
uncorrelated specialization explicitly consumes covariance0. No converse from
zero covariance to independence is asserted.

Generic contracts keep arbitrary supplied finite spaces and total real
samplers, rather than replacing their domains with six numeric inputs.
Supplied-function combination helpers require the pointwise relation; literal
combination interfaces construct the function. Zero and negative coefficients
are included, while nonreal coefficients and undefined samplers are rejected.

The focused checker owns strict source/consumer and final-statement refusal
gates, plus the two installed layouts and std/WiX consistency. These checks
do not establish distributions, measure probability, statistical inference or
full probability compilation to Lean.
