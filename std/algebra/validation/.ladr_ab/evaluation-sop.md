# First-class evaluation and polynomial span correspondence

Status: authoring, 2026-10-31. Task: selected LADR A–B std interfaces/proofs.

The actual polynomial carrier consists of functions. Bounded-degree spaces
must correspond to spans of monomial functions (2.12), so their evaluation
should reuse existing linear-combination transport. First construct the ordinary
unary evaluation map function_evaluation<X,Y,point>: (X→Y)→Y with value
f(point). X,Y are sets and point belongs to X. An empty X supplies no point;
no value is chosen outside a function's complete input domain. Y is an arbitrary
set, not an overloaded scalar/vector operation. No Field is needed merely to
evaluate a function.

For K nonempty, F a Field<K>, X a set and point in X, prove this map linear
from the existing function_space<K,F,X> to scalar_space<K,F>. Reuse the actual
pointwise operations and Field operations, publishing explicit typed local
functions if returned-call membership needs an intermediate. Do not introduce
a second function-space record or a linearity assumption.

Then connect coefficient evaluation to existing linear_combination and span;
retain native finite-sum specifications, R/C arithmetic and trailing-zero
function equality. Do not replace the function carrier with a coefficient-only
carrier. Work in live Session 54118; save accepted source only at checkpoints.
Current canonical vector_space has 34 statements, polynomial has 40. A new
source/imported gate will validate the evaluation increment independently.

Accepted evaluation checkpoint: vector_space 38 statements, independent caller
9 statements, three expected refusals with valid evaluation facts retained.
See evaluation_acceptance.json for exact hashes and current boundaries.

Monomial lists and their evaluated value lists have passed root Session
construction/entry/carrier probes, with ordinal j representing power j-1.
For the scalar finite-sum bridge, first test the native positive-index sum
successor and index-shift laws, then supply a checked partial-sum trace to the
existing linear-combination uniqueness theorem. No alternate sum selector is
introduced. Function-space transport then reuses evaluation linearity and
linear_map_preserves_combination.

2026-11-01 continuation: keep Session 54118. The scalar finite-sum bridge
uses the native zero-based sum directly; the attempted positive-index shift
route is unused. Its natural-valued capped terms are proof-local. Explicit
integer coverage and carrier facts discharge the partial-sum trace conditions;
the canonical polynomial file remains the accepted 40-statement checkpoint.

The complex scalar bridge has passed in the retained Session: the native
finite polynomial sum equals the existing linear_combination over the actual
complex scalar_space, using an explicit zero-start partial-sum trace and its
already proved uniqueness. The real version is next. Twelve monomial
construction/entry/carrier declarations also pass in Session; no new canonical
polynomial checkpoint is claimed until both source and imported gates pass.

The complete real/complex function bridges passed Session probes, using typed
local aliases and explicit scalar carrier facts for equality congruence. The
first canonical run exposed missing module-level publications of the standard
function_space/scalar_space memberships; four existing carrier theorem calls
were added before the bridge declarations. The canonical polynomial source is
now a 64-statement candidate; its fresh independent gate is pending. Bounded
monomial-span set constructors and subspace probes are still Session-only.

The 64-statement canonical run accepted 62 declarations. Its two function
bridges required explicit function-carrier facts and a final equality chain
after function extensionality, which were available in the authoring context
but absent outside the proof-local pointwise block. Those facts/chain were
added without changing the theorem. A fresh canonical run is in progress.

The corrected 64-statement canonical module passes. Its imported caller needed
the same four public space-carrier releases before invoking the explicit LC
statements. The caller is now 22 statements and its fresh gate is pending.
Three retained-Session monomial controls reject index zero, an out-of-range
index for n=0, and the false i-squared value; a fresh standalone control gate
is running. Full-polynomial closure and actual inherited R/C VectorSpace
values have now passed Session probes and remain unmaterialized.
