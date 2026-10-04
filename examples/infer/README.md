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
equal/    InferEqualityResult (PositiveRealPower, CartTupleShape, …)
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
