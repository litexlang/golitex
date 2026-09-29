# Infer tracers
#
# One Infer*Result / store→infer rule → one `.lit` file.
# Names mirror `InferEqualityResult` / `InferAtomicExceptEqualityResult` variants.
#
# These are **not** proof-search ByBuiltinRule tracers (those live under
# `examples/proof_nodes/`). Here the seed fact is stored first
# (`have` / `let` / occasionally `trust` when the carrier is only introducible
# that way), then a consequence that only appears after infer is checked.
#
# Prefer `have` / `let`. Use `trust` only when typed `have x S` cannot WD the
# carrier yet (same pragmatic escape as some existing proof-node files).
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

B1 reformulation (carrier→sign, order flip, `u-v=0`⇒`u=v`) lives under
`examples/proof_nodes/order/` and `proof_nodes/equality/` as
verify-time builtins, not here.

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
