# Finite-product dependencies

The construction is a bounded set of complete finite functions satisfying the
existing `is_choice_function_for` predicate. All lengths are natural, including
zero. No hypothesis about factor nonemptiness enters the construction itself.

Membership introduction folds the pointwise predicate and uses bounded-builder
membership. Elimination exposes the complete function signature and each
coordinate condition. At zero length the empty tuple belongs vacuously; every
complete function on that domain reconstructs the empty tuple. Extensionality
therefore identifies the product with its singleton.

Finite choice is proved by induction over a local property quantified over
all families of the current length. The base uses a typed name for the actual
empty tuple. In the successor step the family is restricted to the preceding
indices, the induction hypothesis gives a complete prefix selection, and one
member is taken from the final nonempty factor. A checked function by cases
extends the prefix with that member. Every coordinate retains its factor
membership. This proof invokes no Choice or Regularity release.

The existence theorem returns the actual complete selection. The imported
`set_laws::set_with_member_is_nonempty` then supplies the native nonemptiness
predicate. An empty factor excludes every candidate by its coordinate law.

Compatibility with native `index_cart` is proved by both membership directions,
explicit inclusion definitions and set extensionality. It is restricted to the
existing native constructor's legal positive-index/nonempty-family domain.
The source construction handles the zero case independently, without changing
native WD or asserting an out-of-domain native expression.
