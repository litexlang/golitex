# Field linear-equation dependencies

For nonzero `a`, multiplying `b` by `inv(a)` yields a solution of `a*x=b`;
nonzero multiplication cancellation proves uniqueness and the explicit value
of any solution. For an affine equation, adding the inverse of the constant
reduces it to a linear equation. Additive and multiplicative cancellation
prove uniqueness, and the same inverse supplies the witness.

Generic callers keep the nonzero-coefficient and equation premises. The real
caller checks both solution formulas and shows that zero coefficients can give
multiple solutions. Negative callers exercise false or missing conditions,
wrong results, inverse at zero, wrong carrier and arity.

All 17 focused checks pass, including ten final-statement refusals and two
installed layouts, using the task's pinned 1.1.6-beta executable.
