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
# Do not use `trust` to bypass carrier WD. The three legacy indexed-family
# tracers still blocked on WD are tracked in
# `plan/迁移的plan/和example有关.md` (B05); they are not passing acceptance.
#
# Param-type projection under a renamed carrier (prop binder `A`, call-site
# `Carrier`): `atomic/normal_atomic_param_types_renamed_carrier.lit`.
#
# Kernel overview: `src/store_fact_and_infer/README.md`.

## Acceptance

```bash
target/release/litex -f <this-file>
```

Exit 0 is enough.

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
