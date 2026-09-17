# new_pipeline proof-node tracers

One concrete builtin rule or search path → one `.lit` file.
File names mirror Rust variants / structs for easy cross-check.

## Acceptance

```bash
LITEX_NEW_PIPELINE=1 target/release/litex -f <this-file>
```

Exit 0 is enough. No requirement to assert which `searched_proof` variant won.

Stub / not-yet-wired nodes are **omitted** (no SKIP placeholders).
Still open: KnownRewrite, ByDefinition search slot, atomic OrderDual rewrite, exist BuiltinRule.

## Layout

```text
or/           ByBuiltinRule (trichotomy ×3), SelectedBranch, KnownOr, KnownForall
equal/        ByBuiltinRule, KnownEquality, BuiltinStrategy, BuiltinRewrite
atomic/       ByBuiltinRule (order/in/set/set-builder/…), KnownAtomicFact
and/          per-component verify
chain/        adjacent order / equality
exist/        KnownExist, KnownForall
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
