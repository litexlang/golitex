# Extended sequence extrema dependencies

The author corrects Analysis I 6.3.1 to allow extended-real-valued sequences;
6.4.6 needs that domain for the sequence of tail suprema/infima. The definition
therefore uses a full integer tail and literal ExtendedReal return carrier.
Actual range membership and the start value prove its carrier and inhabitance.
Total extended set extrema define both sequence values without exceptional
finite, infinite or empty-tail placeholders; every integer tail is nonempty.

Native preimages translate sequence upper/lower bounds to set bounds, deriving
leastness/greatestness. Set-level strict approach follows by contradiction from
these optimality properties and total extended order. Preimages then return an
original-domain sequence witness. These two general set proofs are shared with
the real-valued sequence module instead of being duplicated there.

Native R inclusion proves the return contract of the actual same-value function
real_tail_as_extended. Its exact domain is preserved; fn_set_member exposes that
signature, and both directions of range equality follow from native preimages.
No function is retagged by an unproved assumption.

The README's negative-start tail takes positive infinity initially and negative
infinity thereafter. Endpoint order exclusions determine its actual supremum
and infimum. Independent callers check every theorem at its full domain, a real
affine tail's same-value embedding, and finite-value/domain/strictness controls.
All evidence remains under experiments; no native source, new axiom, trust or
build is part of this increment.
