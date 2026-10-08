# Infer tracers
#
# One Infer*Result / store→infer rule → one `.lit` file.
# Names mirror `InferEqualityResult` / `InferAtomicExceptEqualityResult` variants.
#
# These are **not** proof-search ByBuiltinRule tracers (those live under
# `examples/proof_nodes/`). Here the seed fact is stored first through
# `have`, `let`, or a typed `forall` binder, then its inferred consequence
# is checked.
#
# Do not use `trust` to bypass carrier WD. The three indexed-family tracers
# now use typed `forall` binders and pass strict verification after the FnSet
# alpha-equality migration. See the B05 acceptance record at
# `plan/迁移的plan/experience/problem_notes/b05-equality-recheck.md`.
#
# Param-type projection under a renamed carrier (prop binder `A`, call-site
# `Carrier`): `atomic/normal_atomic_param_types_renamed_carrier.lit`.
#
# Kernel overview: `src/store_fact_and_infer/README.md`.

## Acceptance

`atomic/cart_exact_function_coordinates.lit` and the migrated
`atomic/in_cart_projection.lit` use ordinary applications after exact Cartesian
membership. They cover zero/one/multiple coordinates, literal and carrier
aliases, and an explicitly restricted function. Old tuple shape/dimension
facts are not published. Struct field order and dependent/guarded fields are
checked in `../stmt_nodes/definition/struct_function_coordinate_bridges.lit`;
invalid fields, calls and guards have executable controls in the exact-domain
negative manifest.

`atomic/in_sequence_space_alias_expand.lit` checks exact finite-sequence and
sequence memberships after carrier and object aliases, including symbolic
length, zero length and multiple return upper bounds. The adjacent
`in_equal_fn_set_expand.lit` uses `have f A` to construct a member of the
function space; a value equal to the space itself is not callable.
Executable out-of-range and callable-space controls are registered in
`../negative/exact_function_domains/manifest.json`.

Callable-field range and indexed-family consequences are covered by
`atomic/field_fn_range.lit` and `atomic/field_indexed_family.lit`.
`equal/nonzero_real_square.lit` checks positive membership transported from
a nonzero real square while retaining the negative/zero/complex boundaries.

`atomic/set_builder_projection_replay.lit` proves a self-carrier builder equality
by extension, rechecks the stored equality, and checks a different builder's
carrier and defining condition. Exact already-visible builder consequences are
not recursively inferred again; new consequences are retained.

```bash
target/release/litex -strict -f examples/infer/atomic/set_builder_projection_replay.lit
```

Require exit 0, root `success: true`, and `session_error: null`.

`atomic/choice_function_pointwise.lit` stores a positive choice-function
certificate, releases its existing pointwise definition, then checks a fiber
membership through the ordinary known-forall path.

```bash
target/release/litex -f <this-file>
```

Require exit code 0 and top-level JSON `success: true`.

## Layout

```text
equal/    InferEqualityResult (PositiveRealPower, …)
atomic/   InferAtomicExceptEqualityResult (InFact shape expose, subset, …)
```

B1 leftovers that stay verify-time builtins live under
`examples/proof_nodes/order/` and `proof_nodes/equality/`:
order-sign from literal bound, `OrderFlipMulMinusOne`, and
`EqualFromKnownDifferenceZero`. Carrier → sign (`N` / `R+` / `R-` / `R*`)
is eager infer again — see `atomic/in_signed_standard_set_*.lit`.

## Run all

```bash
export PATH="/usr/bin:/bin:$PATH"
fail=0
while IFS= read -r f; do
  echo "=== $f ==="
  target/release/litex -f "$f" || fail=1
done < <(find examples/infer -name '*.lit' | sort)
exit $fail
```

`atomic/in_signed_standard_set_nonzero_from_sign.lit` publishes `x != 0` from strict positive/negative standard carriers before later inferred division/modulo facts need WD. Nonnegative N and unsigned R do not supply nonzero. The common-divisor builder demonstrates explicit subset proof for its natural carrier; direct carrier automation remains a separate limitation.

`atomic/subset_finite_upper_bound.lit` publishes lower-set finiteness from a stored inclusion and an available finite upper certificate; missing or infinite upper certificates do not trigger it.

`atomic/strict_lower_bound_positive.lit` publishes positivity from a stored strict lower bound and an available nonnegative-bound proof; the original log goal keeps its `1 < x` premise.

`atomic/weak_integer_lower_bound_in_n.lit` publishes N membership from a stored
weak lower bound plus integer and nonnegative-bound certificates. It covers
both order spellings, a fractional positive bound, and the original induction
comparison WD shape. The focused `weak_integer_lower_bound_in_n` tests retain
both premise proofs and citations, reject missing-domain/negative-bound/strict
carrier conclusions, and check local scope, failed-statement rollback and
ordinary/strong induction.

`atomic/normal_atomic_expand_bounded_wd.lit` constructs a set whose defining
predicate contains a finite-sequence existential. Optional definition children
whose WD is unavailable at the caller ceiling are skipped; that does not abort
the already checked seed or increase its permissions. The focused
`normal_atomic_expand_bounded_wd` Rust tests retain invalid-call and false-fact
rejection, renamed-carrier parameter projection, and the original Direct-level
WD boundary.
