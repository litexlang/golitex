# Rational/real sequence consistency dependencies

Source: Tao Analysis I 6.1.4, 6.1.15 and the consistency assertion following
6.1.16. The scalar absolute distance and epsilon predicate are unchanged.

The source rational index tail is proved to contain every integer n>=start.
The rational_tail_as_real template constructs a real-valued function on the
literal actual tail, evaluating the original rational function at that n.
It neither retags a function by an assumed equality nor changes its domain.

Rational density gives rational-radius Cauchy -> real-radius Cauchy. The
reverse specializes real radii to positive rationals. Both proofs transport
actual pointwise values and preserve the same integer cutoff. They precede
limit existence and use no completeness in the radius-consistency argument.

Actual positive reindexes agree termwise, so native limit preservation gives
the source epsilon candidate. Existing rational Cauchy native existence and
source uniqueness give unique genuine limits. Native existence and source
convergence are published before partial-selector equality is formed. This
proves the actual selected native real equals the source selected limit.

Rational bounded-by transports directly, including zero. Real bounded-by
transports to a larger positive integer rational bound by Archimedean order.
Existential boundedness transports both directions. There is no assumption,
axiom, new native feature, trust debt, alternate real model or domain fallback.
