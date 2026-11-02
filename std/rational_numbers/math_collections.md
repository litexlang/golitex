# Rational-square gap dependencies

`rational_square_not_two(x Q)` assumes no positivity or reduced representation
of its argument. The native `rational_has_unique_reduced_fraction(x)` supplies
integers `p`, positive natural `d`, `x=p/d` and `gcd(p,d)=1`. Assuming `x^2=2`
gives `p^2=2*d^2`. The prime-power divisor law makes `p` even. The actual integer
`k=p/2` then gives `d^2=2*k^2`, so `d` is even as well. Two divides the gcd,
contradicting `gcd(p,d)=1`; the final contradiction is checked with the exact
remainder of one modulo two. No least-numerator or positivity premise is
silently imposed.

`rational_square_two_straddle(epsilon R+)` constructs its rational witness
using native real roots and the reserved rational-density theorem. If the
radius is less than the positive root, choose a rational strictly between
`sqrt(2)-epsilon` and `sqrt(2)`. Otherwise choose it between zero and the root.
Both cases give a positive rational below the root whose translate is above
it, and ordinary square order gives the strict straddle. The conclusion only
requires nonnegativity. The theorem includes every source positive rational
radius and also positive real radii.

Native integer/rational carriers, quotient arithmetic, ordered-field laws,
absolute values, integer parts, natural upper bounds and rational midpoint
density are checked separately in the source correspondence workspace. They
are reused foundations, not additional public aliases in this module. No
axiom, trust, Choice, Regularity, kernel repair or new native Obj is introduced.
