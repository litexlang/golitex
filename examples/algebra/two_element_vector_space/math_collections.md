# Two-element scalar-line dependencies

The actual two-element Field supplies vector zero, addition and scalar
multiplication. Releasing the imported Field's struct definition exposes its
existing laws. Associativity and commutativity of addition give the vector
addition axioms, and field negation supplies additive inverses. Multiplicative
associativity, both distributive laws and the field identity give the scalar
action axioms. The resulting tuple is checked against the existing VectorSpace
struct; no new field, vector-space axiom, coercion or native rule is added.

The native identity map has every field element in its range and only zero in
its kernel. The native zero map sends both distinct elements to zero, so its
kernel is the full carrier and it is not injective. The generic zero-kernel
criterion recovers injectivity for the identity. Negative callers check false
kernels, zero-map injectivity, wrong values and field carriers.

The example proves that the one-element list containing `1` is independent and
spans, then uses the generic basis-dimension theorem to obtain dimension `1`.
It also proves the zero list dependent and not a basis. At that checkpoint,
21 focused checks passed, including 14 final-statement refusals and two installed
layouts.

The current extension derives identity rank/nullity `(1,0)` and zero-map
rank/nullity `(0,1)` using the existing inherited image and kernel spaces,
finite-dimensional guards and rank-nullity theorem. The constant-one function
is proved non-linear. All 29 extended focused checks pass, including 22
final-statement refusals and both installed layouts.
