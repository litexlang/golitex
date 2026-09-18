# new_pipeline proof-node tracers

One concrete builtin rule or search path → one `.lit` file.
File names mirror Rust variants / structs for easy cross-check.

## Acceptance

```bash
LITEX_NEW_PIPELINE=1 target/release/litex -f <this-file>
```

Exit 0 is enough. No requirement to assert which `searched_proof` variant won.

Stub / not-yet-wired nodes are **omitted** (no SKIP placeholders).
Still open (non-rewrite): empty atomic builtin-rule families (`NormalAtomic` / several `Not*` / `FnEqualIn`); more exist builtins.
Equality BuiltinRewrite: only ClosedNumericEqualSubstitution (no general known-equality subterm rewrite).
OrderDual rewrite: `atomic/by_builtin_rewrite/order_dual.lit`.
KnownRewrite: `atomic/by_known_rewrite/reflexivity.lit`, `symmetry.lit`.
WD negatives (must fail): `examples/new_pipeline_wd_negative/`.

## Layout

```text
or/           ByBuiltinRule (trichotomy ×3), SelectedBranch, KnownOr, KnownForall
equal/        ByBuiltinRule, KnownEquality, BuiltinStrategy, MatchingOneArgByOne, BuiltinRewrite (ClosedNumericEqualSubstitution only)
atomic/       ByBuiltinRule, KnownAtomicFact, ByDefinition, BuiltinStrategy (PosAddPos), BuiltinRewrite (OrderDual), KnownRewrite (Reflexivity/Symmetry)
and/          per-component verify
chain/        adjacent order / equality
exist/        ByBuiltinRule (real-line), KnownExist, KnownForall
forall/       introduce → assume → then
forall_iff/   both directions
not_forall/   via derived counterexample exist
```

## Run all

```bash
export PATH="/usr/bin:/bin:$PATH"
fail=0
while IFS= read -r f; do
  echo "=== $f ==="
  LITEX_NEW_PIPELINE=1 target/release/litex -f "$f" || fail=1
done < <(find examples/new_pipeline_proof_nodes -name '*.lit' | sort)
exit $fail
```
