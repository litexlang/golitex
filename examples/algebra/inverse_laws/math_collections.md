# Group inverse law dependencies

The inverse of the identity and inverse involution follow from the existing
inverse and uniqueness laws. Right-inverse uniqueness uses cancellation.
Checking `inv(b)*inv(a)` as an inverse of `a*b` gives the reversed product
law. Right cancellation then yields uniqueness for `x*a=b`, whose witness is
`b*inv(a)`. The inverse-commutation result keeps the premise that the original
elements commute.

The generic contracts are accompanied by integer, one-point and
noncommutative callers. In the Heisenberg group, the two inverse orders and
the two proposed right-equation witnesses are evaluated separately. The
one-point construction checks its carrier and operation types explicitly.
Negative callers exercise incorrect values and orders, omitted premises and
invalid group or element types.

The focused checker verifies all 25 cases, including 15 final-statement
refusals and both installed layouts. It uses the task's pinned 1.1.6-beta
executable; this is not a full compiler or release verification.
