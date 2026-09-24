# new_pipeline proof-node tracers

One concrete builtin rule or search path → one `.lit` file.
File names mirror Rust variants / structs for easy cross-check.

When a kernel feature is **new** or an existing surface is **updated /
widened**, add a **new** `.lit` here (or under the matching
`../wd` / `../stmt_nodes` / `../wd_negative` / `../infer` folder) in the same turn.
Do not leave acceptance only in `examples/tmp.lit`.

## Writing style

Prefer `have … = …` and `forall` binders. Do **not** use `trust` to fake
definitions or ambient assumptions in these tracers (see
`examples/new_pipeline/stmt_nodes/unsafe/` for trust-stmt coverage).

## Acceptance

```bash
LITEX_NEW_PIPELINE=1 target/release/litex -f <this-file>
```

Exit 0 is enough. No requirement to assert which `searched_proof` variant won.

Stub / not-yet-wired nodes are **omitted** (no SKIP placeholders).
Still open (non-rewrite): empty atomic builtin-rule families (`NormalAtomic` /
several remaining `Not*`); more exist builtins;
secondary subset leaves (set-minus / power-set / cart / subset-transitivity);
strict-order duals of add/mul algebra; MatchingOneArgByOne beyond the traced constructors;
equality-identity builtins (more power/log/mod/min/max/…); richer `!=` / set-relation duals.
Order wave now includes power/sqrt/log, mod bounds, sub↔0 bridges, order
transitivity, div monotone/shrink (pos and neg divisor), div↔product bridges,
literal numeric bound chase, integer successor/adjacency/predecessor, positive
even `1 < i`, finite-set max/min member bounds, union card `<=` sum, surjection
codomain card `<=` domain, and basic `finite_set_size` card bounds.
Equality BuiltinRule power laws (Stage B wave 1): `a^m * a^n = a^(m+n)`,
`(a^m)^n = a^(m*n)`, `(a*b)^n = a^n * b^n`, `1/a = a^(-1)`, `a/b = a * b^(-1)`
under `examples/new_pipeline/proof_nodes/equal/by_builtin_rule/power_*.lit` and
`reciprocal_*` / `quotient_*`.
Equality BuiltinRule identities (Stage B wave 2): power `1^a` / `0^n`; sqrt /
abs / log families; mod `0 % a`, `a % 1`, `1 % m`, nested absorption — see
`one_to_any_power.lit`, `zero_to_pos_nat_power.lit`, `sqrt_*.lit`, `abs_*.lit`,
`log_*.lit`, `zero_mod.lit`, `mod_one.lit`, `one_mod_at_least_two.lit`,
`nested_same_mod_absorption.lit`.
Equality BuiltinRewrite: ClosedNumericEqualSubstitution (equal + atomic) and
atomic KnownEqualObjSubstitution.
No equality KnownRewrite slot (dead; = uses EqualIr / known_equivalence_classes graph).
OrderDual rewrite: `atomic/by_builtin_rewrite/order_dual*.lit`.
KnownRewrite: `atomic/by_known_rewrite/reflexivity.lit`, `symmetry.lit`.
WD negatives (must fail): `examples/new_pipeline/wd_negative/`
(including `fn_app_not_in_function_set.lit`: `have f R` then `f(a)`).
WD gallery (positives for done Obj/Fact WD): `examples/new_pipeline/wd/`.

## Layout

```text
or/           ByBuiltinRule (trichotomy ×3, NaturalZeroOrAtLeastOne), SelectedBranch,
              KnownOr, KnownForall
equal/        ByBuiltinRule (FnSet / AnonymousFn / SetBuilder alpha-equal,
              EqualToObjWithFreeParamsLookup, Calculation closed decimal +
              arithmetic_ops), EquivalenceClass, ObjectDefinition
              (identifier / fn / template), BuiltinStrategy, MatchingOneArgByOne,
              KnownForall (+ViaSymmetry), BuiltinRewrite
              (ClosedNumericEqualSubstitution + arithmetic_ops)
atomic/       ByBuiltinRule (incl. NotIn closed/list/intersect/union; In
              union/intersect/set_minus/family_union/index_union + R-arithmetic
              closure; LessEqual abs + add/sub/mul order algebra + triangle/
              reverse-triangle/sandwich; Subset list-set/union/intersect from
              members or operand upper bounds; Greater from known less), KnownAtomicFact,
              ByDefinition (user prop + builtin official defs; see
              atomic/by_definition/ and src/.../by_definition_design.md),
              BuiltinStrategy (PosAddPos), KnownForall, BuiltinRewrite
              (ClosedNumeric, KnownEqualObj, OrderDual, ClosedNumeric arithmetic_ops),
              KnownRewrite (Reflexivity/Symmetry)
and/          per-component verify
chain/        adjacent order / equality
exist/        ByBuiltinRule (real-line, equality-from-membership, nonempty-member),
              KnownExist, KnownForall
forall/       introduce → assume → then
forall_iff/   both directions
not_forall/   via derived counterexample exist
obj_wd/       FnSet / AnonymousFn / SetBuilder binder WD; cart_dim / proj / ObjAtIndex
```

## Run all

```bash
export PATH="/usr/bin:/bin:$PATH"
fail=0
while IFS= read -r f; do
  echo "=== $f ==="
  LITEX_NEW_PIPELINE=1 target/release/litex -f "$f" || fail=1
done < <(find examples/new_pipeline/proof_nodes -name '*.lit' | sort)
exit $fail
```
