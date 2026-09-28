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
MatchingOneArgByOne beyond the traced constructors;
deeper aggregate (sum split / bijective reindex); nested-mod algebra;
complex `re`/`img` equalities; richer `!=`.
NotSubset / NotSuperset duality (A7): known `not B $superset A` proves
`not A $subset B`, and known `not B $subset A` proves `not A $superset B` —
see `not_subset_from_known_not_superset.lit`,
`not_superset_from_known_not_subset.lit`.
Subset leftovers (A8): `union(A,B) $subset union(C,D)` componentwise;
`range` / `closed_range` into `N`/`N+`/`Z`/`Q`/`R` —
see `subset_union_from_componentwise.lit`,
`subset_integer_range_numeric_carrier.lit`.
NotEqual leftovers (A9 partial): nonempty ⇒ `A != {}`;
`n $in N` ∧ `1 <= n` ⇒ `n != 0`; `a != 0` ⇒ `a^n != 0`;
`a != 0` ∧ `b != 0` ⇒ `a/b != 0`; `a*b != 0` ⇒ `a != 0`;
`0 < a` ⇒ `sqrt(a) != 0`; `a != 0` ⇒ `a^2+b^2 != 0`;
`a != -b` ⇒ `a+b != 0`; membership contradiction `x $in A`, `y $notin A`
⇒ `x != y` — see `not_equal_*.lit`.
Strict order add/mul (A10 partial): `a < b` ⇒ `a+c < b+c`;
`0 < k` and `a < b` ⇒ `a*k < b*k` — see
`less_add_right_congruence_strict.lit`,
`less_mul_right_positive_monotone_strict.lit`.
Order wave now includes power/sqrt/log, mod bounds, sub↔0 bridges, order
transitivity, div monotone/shrink (pos and neg divisor), div↔product bridges,
literal numeric bound chase, integer successor/adjacency/predecessor, positive
even `1 < i`, finite-set max/min member bounds, union card `<=` sum, surjection
codomain card `<=` domain, and basic `finite_set_size` card bounds.
Equality BuiltinRule power laws (Stage B wave 1): `a^m * a^n = a^(m+n)`,
`(a^m)^n = a^(m*n)`, `(a*b)^n = a^n * b^n`, `1/a = a^(-1)`, `a/b = a * b^(-1)`
under `examples/new_pipeline/proof_nodes/equal/by_builtin_rule/power_*.lit` and
`reciprocal_*` / `quotient_*`.
Equality BuiltinRule identities (Stage B wave 2):
`1^a=1` (`N`), `0^n=0` (`N+`); `sqrt_*` square/zero/one/of_square/product/
quotient; `abs_*` negation/product/square; `log_*` base_self/of_one/of_power/
arg_power/product/quotient/reciprocal/change_of_base; `zero_mod`, `mod_one`,
`one_mod_at_least_two`, `nested_same_mod_absorption`.
Four files use narrow `trust` only for current WD holes (quotient positivity /
sqrt-denom / log-nonzero / mod-result in `Z`); remove when WD catches up.
Equality BuiltinRule identities (Stage B wave 3):
`min`/`max` idempotent + commutative; `abs(abs(a))=abs(a)`;
`exp(ln(x))=x` (`R+`); `ln(exp(x))=x` (narrow `trust exp(x) $in R+` for ln WD);
`floor(n)=n` / `ceil(n)=n` (`Z`); `a % a = 0` (`a != 0`) — see `min_*.lit`,
`max_*.lit`, `abs_abs_absorption.lit`, `exp_of_ln.lit`, `ln_of_exp.lit`,
`floor_of_integer.lit`, `ceil_of_integer.lit`, `mod_self_zero.lit`.
Equality BuiltinRule identities (Stage B wave 4):
`floor(ceil(n))=n`, `ceil(floor(n))=n` (`Z`); `sqrt(a^2)=abs(a)` — see
`floor_of_ceil_of_integer.lit`, `ceil_of_floor_of_integer.lit`,
`sqrt_of_square_equals_abs.lit`.
Equality BuiltinRule identities (Stage B wave 5):
`quot(a,1)=a`; `quot(a,a)=1` (`N+`); `lcm` commutative / idempotent-abs;
`gcd` commutative / idempotent-abs / left-right zero-abs (narrow `trust a != 0`
for current gcd WD); `(n+1)!=(n+1)*n!` (narrow `trust n! $in N` for factorial
carrier / mul WD) — see `quot_*.lit`, `lcm_*.lit`, `gcd_*.lit`,
`factorial_successor.lit`.
Equality BuiltinRule identities (Stage B wave 6):
`abs(a)=a` (`0 <= a`); `abs(a)=0-a` (`a <= 0`); `sign(a)=1` (`0 < a`);
`sign(a)=0-1` (`a < 0`); ordered `min`/`max` — see `abs_nonneg_equals_self.lit`,
`abs_nonpos_equals_negation.lit`, `sign_of_*.lit`, `max_*_when_less_equal.lit`,
`min_*_when_less_equal.lit`.
Equality BuiltinRule identities (Stage B wave 7):
`a % gcd(a,b)=0` / `(a*b)%a=0` (nonzero divisor; gcd uses narrow trust for WD);
`a=b` from two-sided `<=`; `a-b=0` from `a=b`; zero-product cancel;
`sign(0-a)=0-sign(a)`; `sign(a)*abs(a)=a`; `abs(a)=sign(a)*a`;
`sign(a*b)=sign(a)*sign(b)` (sign nodes use narrow `trust sign(_) $in R`);
`a=c-b` from known `a+b=c` — see `gcd_divides_argument.lit`,
`product_mod_factor_zero.lit`, `equality_from_two_sided_weak_order.lit`,
`diff_zero_from_equal_operands.lit`, `zero_product_cancel.lit`,
`sign_of_negation.lit`, `sign_times_abs_equals_arg.lit`,
`abs_equals_sign_times_arg.lit`, `sign_of_product.lit`,
`subtraction_from_known_addition.lit`.
Equality BuiltinRule identities (Stage B wave 9):
set empties / commutative / idempotent; intersect-from-subset;
empty-from-not-nonempty; power_set cardinality — see `union_empty_*.lit`,
`intersect_empty_*.lit`, `set_minus_*.lit`, `union_commutative.lit`,
`intersect_from_subset.lit`, `empty_set_from_not_nonempty.lit`,
`power_set_finite_set_size.lit`, plus associative / distributive / De Morgan
(`union_associative.lit`, `intersect_associative.lit`,
`intersect_union_distributive.lit`, `set_minus_*_de_morgan.lit`,
`intersect_set_minus_self_empty.lit`).
Equality BuiltinRule identities (Stage B wave 11):
union absorption / set-minus recovery; empty from size 0; cart proj /
tuple index; finite-set size set-minus/union; closed_range singleton;
sum/product single-term; reduce↔sum bridges; pow-of-log inverse — see
`union_absorption_from_subset.lit`, `cart_proj_factor.lit`,
`tuple_component_at_index.lit`, `finite_set_size_*.lit`,
`sum_single_term.lit`, `reduce_add_zero_equals_sum.lit`,
`pow_of_log_inverse.lit`, etc.
Equality BuiltinRule identities (Stage B wave 12):
union/set_minus decomposition; set_minus∩self; complex `re`/`img`/`C_abs`
basics; nested mod absorption; sum/product last-term split; finite-set
sum/product list expansion — see `union_set_minus_decomposition.lit`,
`set_minus_intersect_self.lit`, `re_of_*.lit`, `img_of_*.lit`,
`complex_abs_of_imaginary_unit.lit`, `mod_nested_divisible_absorption.lit`,
`sum_split_last_term.lit`, `product_split_last_term.lit`,
`finite_set_sum_list_expansion.lit`, `finite_set_product_list_expansion.lit`.
Equality BuiltinRule identities (Stage B wave 13) + closed trig:
`e=exp(1)`, `ln(e)=1`; `sin/cos/tan` specials + Pythagorean; complex
`re/img` on reals and `a+b*i`; `C_abs` on nonnegative/imag-scaled;
`range`/`closed_range` literal expansion; `power_set` empty/singleton;
`family_union({})`; empty-factor `cart`; union-over-intersect; set_minus
chain; constant `fn_range` (literal anonymous ok); `seq`/`finite_seq` as FnSet —
see `euler_equals_exp_one.lit`, `sin_of_zero.lit`, `pythagorean_identity.lit`,
`closed_range_literal_expansion.lit`, `seq_equals_fn_on_n.lit`, etc.
Equality BuiltinRule identities (Stage B wave 14 / Obj P0–P2):
`index_union/intersect/cart` empty-index + singleton union; `finite_seq(S,0)`;
obviously-empty set-builder; `cot(pi/2)`; `C_abs(a+b*i)^2`; `exp(a+b)`;
`log(a^b,c)`; `re/img` of product; trig angle-add; reduce single-term with
add/0 — see `index_*_empty_index.lit`, `cot_of_half_pi.lit`,
`complex_abs_squared_of_rect_form.lit`, `exp_of_sum.lit`, `sin_of_sum.lit`,
`reduce_single_term_with_add_zero.lit`. Atomic: finite_seq finiteness —
`is_finite_set_finite_seq_zero.lit`, `is_finite_set_finite_seq_from_finite_codomain.lit`.
Empty absolute ∩ settled: no `family_intersect({})={}` (use `index_intersect`);
negative probe `examples/new_pipeline/equal_negative/family_intersect_empty_equals_empty.lit`
(expect exit ≠ 0).
Equality BuiltinRule identities (Stage B wave 15): finite-set Fubini —
nested double-sum swap, and nested = flat sum over `cart(X,Y)` when the
summand is `f((x,y))` — see `finite_set_sum_fubini_swap.lit`,
`finite_set_sum_over_cartesian_product.lit`.
NotIn interval open-endpoint / outside (atomic).
Equality BuiltinRule identities (Stage B wave 10):
empty aggregates `finite_set_sum/product/reduce` and empty-range
`sum`/`product`/`reduce` — see `finite_set_*_empty.lit`, `sum_empty_range.lit`,
`product_empty_range.lit`, `reduce_empty.lit`.
Greater add/mul congruence (A10): `greater_add_*_congruence_strict.lit`,
`greater_mul_right_positive_monotone_strict.lit`.
Equality BuiltinRule identities (Stage B wave 8):
Euclidean `a=d*quot(a,d)+(a%d)`; `(a-(a%b))%b=0` (narrow nonzero-divisor trust);
`a=0` from known `a^2+b^2=0`; `(-1)^(2*m+1)=-1`;
`lcm(a,b)*gcd(a,b)=abs(a*b)` (narrow lcm/gcd WD trust) — see
`quot_euclidean_decomposition.lit`, `mod_dividend_minus_remainder_zero.lit`,
`square_sum_component_zero.lit`, `minus_one_odd_natural_power.lit`,
`lcm_gcd_product_abs.lit`.
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
              arithmetic_ops + integer_sqrt_log + complex_nested), EquivalenceClass, ObjectDefinition
              (identifier / fn / template), BuiltinStrategy, MatchingOneArgByOne,
              KnownForall (+ViaSymmetry), BuiltinRewrite
              (ClosedNumericEqualSubstitution + arithmetic_ops)
atomic/       ByBuiltinRule (incl. NotIn closed/list/intersect/union/set_minus;
              NotIsFiniteSet standard infinite + set_minus; In
              union/intersect/set_minus/family_union/index_union + R-arithmetic
              closure; LessEqual abs + add/sub/mul order algebra + triangle/
              reverse-triangle/sandwich; Subset list-set/union/intersect from
              members or operand upper bounds; Greater from known less), KnownAtomicFact,
              ByDefinition (user prop + builtin official defs; see
              atomic/by_definition/ and src/.../by_definition_design.md),
              BuiltinStrategy (atomic family: additive_sign / nonzero /
              structural_order / numeric_carrier / set_membership / subset /
              is_finite_set / is_nonempty_set; see atomic/by_builtin_strategy/),
              KnownForall, BuiltinRewrite
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
