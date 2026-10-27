# Finite real-valued sums on vector domains

A separate source function constructor fixes one vector input, real output and
an actual domain D. Numeric sums are reused from real_function_sums. The scalar
module's checked index-inclusion wrapper exposes the dependency needed during
constructor WD; it does not change module visibility or auto-import facts.

Finite source induction combines supplied partial candidates on D. The empty
base transports the full-space constant partial to D through the existing
locality restriction theorem and the supplied coordinate neighborhood.
Continuity is currently proved at a supplied Euclidean interior point; arbitrary
relative-domain continuity remains outside this theorem's explicit contract.
One template and five thms reuse existing rules without new native machinery.
