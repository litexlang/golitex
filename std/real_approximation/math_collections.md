# Absolute-error proof dependencies

The single predicate has contract
`is_epsilon_close(x R,y R,epsilon R+) := abs(x-y)<=epsilon`.
The module has sixteen named theorems. Real and rational identity theorems
have different quantified radius domains; neither replaces one domain with
the other silently.

Absolute-value bounds use the native nonnegative/negative branches and explicit
negation steps. Closeness identity chooses half the nonzero distance; for
rational points this is a positive rational radius. Symmetry, addition,
subtraction and transitivity use actual difference identities and native
triangle inequalities. Betweenness uses the proved two-sided absolute bound;
reversing the endpoint arguments covers the other source order. Scaling keeps
the source's nonzero factor so its resulting radius remains positive.

For multiplication, actual perturbations `a=y-x` and `b=w-z` give
`yw-xz=az+bx+ab`. Multiplicativity, two triangle inequalities and three explicit
monotone additions yield the full source radius, including `epsilon*delta`.
No boundedness hypothesis on the four points is added. The sharp example
`x=z=1`, `y=w=2`, `epsilon=delta=1` has error three; radius two is a false control.

Natural-power compatibility uses induction from zero. Integer-power
compatibility splits the exponent sign, reuses the natural theorem and proves
absolute reciprocals from multiplicativity and cancellation. Its base is
nonzero; the natural theorem independently covers a zero base and exponent.
The existing real_series positive-exponent helper remains compatible; it has
not been removed or renamed.

The proofs reuse native real arithmetic, powers, absolute value and induction.
There are no user axioms, trust statements, native implementation changes,
general normed-space claims or new convergence interfaces. Source statements,
full-domain imported callers, applications and exact negative boundaries are
recorded under experiments/std-library-development.


The source 5.3 support estimates remain general real scalar inequalities.
Bounded-product error uses x and w, so no mixed product is lost. Its raw real
bounds admit zero errors and zero magnitude bounds. Reciprocal error assumes
nonzero real inputs and positive lower bounds on each absolute value. The
proof expands the difference of reciprocals, proves absolute quotients using
multiplicativity and cancellation, and multiplies explicit positive-denominator
inequalities. It does not assume an unproved reciprocal comparison.
