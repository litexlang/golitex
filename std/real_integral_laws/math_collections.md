# Mathematical interfaces for Riemann absolute-value bounds

A finite Riemann candidate is a relation among an actual complete real
function, ordered endpoints and a real value; it is not an unconditional
selected value. Let `g(x)=abs(f(x))` on the sorted closed interval and let
`I` and `J` be supplied candidates for `f` and `g`. For `a<=b`, the pointwise
inequalities `f<=g` and `-f<=g`, together with candidate scaling and comparison,
give `I<=J` and `-I<=J`, hence `abs(I)<=J`.

Reversing both candidates gives the arbitrary-orientation inequality
`abs(I)<=abs(J)`. The equal-endpoint case is included. The sorted interval
must lie inside the actual domain D, which may itself be exactly the interval.

If `f` is continuous at each interval point and `g=abs(f)` on all D, the
pointwise absolute-value continuity rule makes `g` continuous there. Native
Riemann integrability of continuous functions supplies both candidates and
the preceding bound. This does not prove the stronger result that an arbitrary
Riemann-integrable function has an integrable absolute value. Neither inequality
computes an integral value or covers unbounded/improper integrals.

For two candidate integrals I and J, native integral subtraction gives the
candidate I-J for `d=f-g`. Applying the absolute-value bounds to d and a
supplied candidate K for `abs(d)` proves the corresponding error estimates in
both orientations. This does not assert a candidate for K without evidence.
