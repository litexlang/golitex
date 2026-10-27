# Real scalar regularity

## Values and propositions

Finite derivative candidates, existence and selected derivative functions are
reused from real_multivariable. C^k and smoothness are source propositions about
those functions. They introduce no new value constructor. Unary R input and
one cart_n(R,n) input have distinct names and complete actual domains.

## Open-domain finite regularity

Ordinary continuity is the zero-order clause. Every positive order supplies
all-point derivative existence on the original open domain D and continuity of
the corresponding canonical derivative function on exactly D. For a scalar
vector-input function this quantifies each ordered finite coordinate path.
No implicit extension, domain restriction or coordinate-count permutation is
part of the definition. Smoothness quantifies all finite orders.

## Construction and consequences

The unary constructor uses checked continuous profiles. The scalar constructor
uses a continuous candidate function for each positive order and path, exposed
by is_continuous_ordered_partial_on. Lower regularity includes C^0. Constant
functions on full spaces are proved smooth for arbitrary finite orders; there
is no trusted smoothness axiom. Relative continuity on isolated domains is
still distinct from these open-domain classes.

## Conditional exchange

C^2 continuity and the open Euclidean neighborhood feed the existing native
Schwarz rule. The source theorem compares supplied candidate values on reversed
length-2 paths. Euclidean distance is connected to the raw coordinate-difference
norm ball by an explicit source equality and inclusion proof. This does not
establish higher permutation invariance or D^alpha semantics.

## Ownership and verification

Five ordinary props and twelve checked source thms live in this optional module.
Native derivative/partial definitions, constant strategies, continuity, and the
existing Schwarz BT are dependencies. There is no new kernel schema, trust,
selector, global state or implicit inference rule. Public examples and installed
refusal-and-liveness controls record actual usability; task receipts remain in
the maintained local inventory.
