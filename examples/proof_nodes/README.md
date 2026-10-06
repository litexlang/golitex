# Proof-node tracers

One concrete builtin rule or search path → one `.lit` file.
File names mirror Rust variants / structs for easy cross-check.

When a kernel feature is **new** or an existing surface is **updated /
widened**, add a **new** `.lit` here (or under the matching
`../wd` / `../stmt_nodes` / `../wd_negative` / `../infer` folder) in the same turn.
Do not leave acceptance only in `examples/tmp.lit`.

## Writing style

Prefer `have … = …` and `forall` binders. Do **not** use `trust` to fake
definitions or ambient assumptions in these tracers (see
`examples/stmt_nodes/unsafe/` for trust-stmt coverage).

## Acceptance

```bash
target/release/litex -f <this-file>
```

Exit 0 is enough. No requirement to assert which `searched_proof` variant won.

Stub / not-yet-wired nodes are **omitted** (no SKIP placeholders).

## Fixed real trigonometric reflections and double angle

[Cosine double angle](equal/by_builtin_rule/cos_double_angle.lit) supports
the three standard square forms for `cos(2*x)`, including `cos(x+x)` and
reversed equality. Four separate tracers cover
[sin(pi-x)](equal/by_builtin_rule/sin_pi_reflection.lit),
[cos(pi-x)](equal/by_builtin_rule/cos_pi_reflection.lit),
[sin(pi/2-x)](equal/by_builtin_rule/sin_half_pi_reflection.lit), and
[cos(pi/2-x)](equal/by_builtin_rule/cos_half_pi_reflection.lit).
Exact numeric pi coefficients and addition of a negated argument use the same
structural leaves. The enclosing equality must establish real-argument WD;
the leaves generate no search obligations or recursive trig expansions.
Focused `trig_reflections_double_angle_tests` retain cold acceptance,
false sign/angle/coefficient controls, partial-call and complex-domain WD,
actual stored-fact reuse, Detailed evidence and ten-language Normal output.
The [acceptance record](experience/problem_notes/trig-reflections-double-angle-2026-10-05.md)
links fixed source/binary receipts and the before/after journal.

## Sequence and struct contracts

[Exact function-space membership](atomic/by_builtin_strategy/exact_function_space_membership.lit)
checks complete domains with numeric return upper bounds, carrier/object
aliases and symbolic finite length. [Empty parameter domains](forall/empty_parameter_domain.lit)
permit vacuous universals only after the whole goal passes WD; a false bare
conclusion and an undefined consequent remain negative controls.
[Finite-function applications](atomic/by_builtin_strategy/finite_function_application_membership.lit)
check stored cart members and object/carrier aliases, coordinate values and
types, repeated and symbolic values, singleton and empty tuples, and a cart
return value. Dedicated negative fixtures reject an alias's out-of-range call,
an unsupported coordinate carrier and a wrong complete length at their actual
WD, search and domain stages.
[Both function bodies](equal/by_object_definition/by_fn_application/both_function_bodies.lit)
retains checked bounded normalization on both equality sides and explicit
extensionality one application layer at a time. The
[negative manifest](../negative/exact_function_domains/manifest.json) checks
short/empty domains, guards, extensionality, callable-set confusion and
publication boundaries. These tracers do not certify the still-pending new
tuple/cart syntax or its complete property matrix.

[Function-value parameter applications](equal/by_object_definition/by_fn_application/function_value_parameter_application.lit)
retain the argument groups of a returned function when substituting it into
another checked body. The exact `first(mk(7)) = mk(7)(1)` step and a two-input
returned function verify. Wrong groups, complete lengths, inner guards and
coordinate values have executable negative partners. The vec/dot consumers
retain their original symbolic body expansions and stored theorem use.

[Function graphs and empty domains](equal/by_builtin_rule/function_empty_domain_graph.lit)
distinguish a function value's empty graph/image from a nonempty space of
empty-domain functions. Constant singleton images retain an actual input and
its guards; FnRange WD retains complete-domain sources, including returned
functions. The dedicated `function_graph` gate checks aliases, nested spaces,
ten output languages, false graph/image claims and failed publication. Three
executable graph controls are in the negative manifest. This does not certify
cart 0/1 syntax or the full remaining property matrix.

[Return-space carrier aliases](atomic/by_builtin_strategy/function_space_return_carrier_aliases.lit)
retain checked equality paths and constructive nested FnSet/cart existence.
[Nested sequence spaces](atomic/by_builtin_strategy/nested_sequence_space_nonempty.lit)
use those witnesses for seq/finite_seq, followed by real returned-function
images. [Closed integer index calculation](atomic/direct_closed_integer_range_membership.lit)
keeps finite-sequence input evidence available at Direct permission. Cyclic
carrier equations, empty nested return spaces and a returned function at an
out-of-range outer index have separate executable negative controls.

[One-based sequences](equal/by_builtin_rule/sequence_one_based.lit) cover
`seq(S) = fn(n N+) S`, finite indices 1 through n, and the empty sequence.
[Struct existential laws](exist/by_known_forall/struct_existential_law.lit)
cover flattened definition publication, existential alpha matching and `obtain`.
Rust `sequence_struct_contract` tests retain bad indices, guards, carriers,
false conclusions, source evidence and scope boundaries.

Displayed finite-set strategies have separate tracers for
[membership](atomic/by_builtin_strategy/list_set_membership.lit) and
[nonmembership](atomic/by_builtin_strategy/list_set_nonmembership.lit).
Their strict gates require exit 0, JSON `success: true` and no `session_error`.
`finite_list_membership_strategy` tests retain false and ill-defined controls,
the inherited search ceiling, stored citations and all requirement certificates.

The [field-expression strategy](atomic/by_builtin_strategy/field_arithmetic_carrier_closure.lit)
retains its constructor tree and terminal proof requirements over Q/R.
The [real constructor builtin](atomic/by_builtin_rule/real_arithmetic_constructor_closure.lit)
composes real function-return leaves through field expressions and integer
powers during comparison goal WD. Its typed tree preserves terminal citations,
integer exponents and the enclosing domain evidence; Direct remains restricted.
The [Cartesian function WD tracer](../wd/real_cart_function_arithmetic.lit)
checks nested absolute-value and quotient definitions. Terminal carrier proofs
are success-only truth evidence; function argument WD remains on the parent
verification stage instead of being replayed at the lower terminal ceiling.
`real_arithmetic_constructor_closure` tests retain wrong carriers/refinements,
zero divisors, bad exponents, partial-function domains, ceilings and rollback.
The [N/Z constructor builtin](atomic/by_builtin_rule/discrete_arithmetic_constructor_closure.lit)
composes natural/integer function returns after the enclosing object WD proof
has checked every call domain. Carrier terminals retain the restricted search
ceiling and signature citations; natural subtraction/negation and nondecreasing
recursive calls remain rejected. The Pascal recurrence is a maintained tracer.
The [nonnegative-sum domain tracer](atomic/by_builtin_rule/nonnegative_sum_domain.lit)
keeps the >= orientation available during restricted function-domain checks,
including nested sums, without reopening a converse strategy.

The [stored numeric superset](atomic/by_known_special_property/standard_numeric_superset.lit)
route cites an existing membership under the intrinsic inclusion table without
fresh premise search. `known_numeric_carrier` tests retain direction, sign,
Direct structural lifting, read-only memory and citation boundaries.
Scalar soundness has maintained tracers for
[real operand closure](atomic/by_builtin_rule/real_arithmetic_operand_carriers.lit),
[real even powers](atomic/by_builtin_rule/even_power_real_carrier.lit),
[exact scalar carriers](atomic/by_builtin_rule/closed_exact_scalar_membership.lit),
[complex inequality](atomic/by_builtin_rule/closed_complex_not_equal.lit) and
[real-valued complex order](atomic/by_builtin_rule/closed_complex_real_order.lit).
Their strict CLI gates require exit 0, success true and no session_error.
`field_arithmetic_carrier_strategy` tests check the real-base evidence,
coordinate evidence, domain/false controls and inherited child ceilings.

[Positive differences](atomic/by_builtin_rule/greater_from_positive_difference.lit)
cover saved `0 < b - a` and `b - a > 0` premises for strict real order.
`positive_difference_order` tests retain the cited premise and reject weak
bounds, the opposite conclusion, missing premises, nonreal operands and leaked
local assumptions.

## Fundamental equality examples

Exact decimal normalization, guarded imaginary division and finite aggregates
have maintained tracers:
[numeric normalization](equal/by_builtin_rule/numeric_normalization.lit),
[imaginary division](equal/by_builtin_rule/imaginary_division.lit),
[aggregate calculation](equal/by_builtin_rule/aggregate_calculation.lit),
[symbolic aggregate identities](equal/by_builtin_rule/aggregate_identities.lit)
and [exact rational inequality](atomic/by_builtin_rule/closed_rational_inequality.lit).
Aggregate rejection controls live in `../test_objs/negative/` and the shared
budget/domain/publication checks in `exec_eval_stmt_tests`.

Known tuple-property routes have dedicated tracers for
[reconstruction](equal/by_known_special_property/tuple_reconstruction.lit),
[stored-equality projection](equal/by_known_special_property/tuple_projection.lit),
and [function projection](equal/by_known_special_property/fn_tuple_projection.lit).
They preserve Membership/Equality citations and do not recursively unfold
functions. Their negative and zero-depth checks live in
`tests/unit/execute/equality_search/known_tuple.rs`.

[Geo coordinate expansion](equal/by_known_special_property/geo_coordinate_expansion.lit)
shows explicit coordinate bridges when composing tuple-valued functions with
dot products and determinants. It preserves the original mathematical goals
and uses no trust or additional assumptions.

[One-step nested function expansion](equal/by_object_definition/nested_call_one_step.lit)
keeps symbolic arguments when the outer body already equals the requested
target. Both the call and the selected body's domain remain checked; the
function-body tests retain wrong-value and missing-guard rejection controls.

[Restricted literal beta](equal/by_object_definition/by_fn_application/restricted_literal_beta.lit)
uses the parent equality's checked WD for the actual anonymous-function
application. Residual truth keeps the definition-premise permissions; named
aliases still check the selected body separately. Both equality orientations
and missing guard/carrier, wrong arity/value, and permission boundaries have
executable function-body regressions.

[Nested-function existential instantiation](exist/by_known_forall/nested_function_alpha.lit)
starts from a witnessed theorem, infers a free callback beneath a literal's
local binder, and preserves whole nested alpha equality when reusing or
releasing its existential conclusion. Local binder capture, changed body,
guards, arity, carriers, witness kind and missing theorem premises remain
checked by the focused `forall_exist_instantiation_tests` regressions.

| What the example demonstrates | Runnable file |
| --- | --- |
| Known `a = b`; prove `a = c` by calculating `b = c` (`b` is `1 + 1`, `c` is `2`) | [Left peer, builtin bridge](equal/by_equivalence_class/via_left_peer_builtin.lit) |
| Known `a = b`; prove `a = c` by alpha identity of `b` and `c` (`fn(x R) R` and `fn(y R) R`) | [Left peer, alpha bridge](equal/by_equivalence_class/via_left_peer_alpha.lit) |
| A named union equals the union with its two symbolic operands swapped | [Union commutativity bridge](equal/by_equivalence_class/via_left_peer_union_commutative.lit) |
| A named anonymous function equals a fresh alpha-equivalent function | [Anonymous-function bridge](equal/by_equivalence_class/via_left_peer_anonymous_fn.lit) |
| A named set builder equals a fresh alpha-equivalent set builder | [Set-builder bridge](equal/by_equivalence_class/via_left_peer_set_builder.lit) |
| Only the right endpoint has a stored peer; reverse its stored edge | [Right peer](equal/by_equivalence_class/via_right_peer_builtin.lit) |
| Both endpoint classes contribute a peer, with two stored edges on each side | [Both peers and multi-edge paths](equal/by_equivalence_class/via_both_peers_multi_edge.lit) |
| Compare two function applications by matching their heads and citing known equality of their arguments | [Matching bridge](equal/by_equivalence_class/via_peers_matching_fn_app.lit) |
| The two sides have the same IR: `x = x` | [SameIr](equal/by_they_are_the_same/by_equal_ir.lit) |
| Function sets differ only by bound parameter names | [FnSet alpha identity](equal/by_they_are_the_same/by_fn_set_alpha_equal.lit) |
| Anonymous functions rename both the parameter and its uses in the body | [AnonymousFn alpha identity](equal/by_they_are_the_same/by_anonymous_fn_alpha_equal.lit) |
| Set builders rename the bound parameter in the condition | [SetBuilder alpha identity](equal/by_they_are_the_same/by_set_builder_alpha_equal.lit) |

The peer examples deliberately leave their bridge unasserted before the goal:
the missing equality must be proved during the class search. The result is
`ByEquivalenceClass::ViaPeers`, with stored paths and a checked bridge.
If all connecting equalities are already stored, the result is `KnownPath`;
see [the stored-path example](equal/by_equivalence_class/path_from_generating_edges.lit).

For `let a = 1 + 1` followed by `a = 2`, calculation and transitivity occur
at different levels. The actual proof has this shape:

```text
a = 2                       ByEquivalenceClass::ViaPeers
  a = 1 + 1                 stored equality from let
  1 + 1 = 2                 ByBuiltinRule::Calculation
```

The class proof combines these steps by transitivity. The calculation child
only proves `1 + 1 = 2`; the stored path supplies its connection to `a`.
Writing `1 + 1 = 2` directly instead selects `ByBuiltinRule::Calculation`
at the outer level. The union example follows the same class structure but
uses `UnionCommutative` as its bridge. The function-application example uses
`ByMatchingOneArgByOne`, whose argument subproof cites a `KnownPath`.

`ByTheyAreTheSame` has `SameIr` and `SameFreeParamShape` cases. The latter's
name refers here to alpha correspondence of bound parameters; genuinely free
identifiers must keep their identities. Carriers, return sets, bodies, and
conditions must agree under the correspondence.

## Further coverage

Still open (non-rewrite): several remaining `Not*` atomic builtin-rule families;
MatchingOneArgByOne beyond the traced constructors;
deeper aggregate (sum split / bijective reindex); nested-mod algebra;
complex `re`/`img` equalities; richer `!=`.
Wave3 exist builtins: `RationalIntegerRatio`, `IntegerMultipleFromZeroRemainder`,
`ArchimedeanReciprocal`, `RealDensityMidpoint` — see
`exist/by_builtin_rule/`. Skipped green tracer for
`RationalPositiveDenominator`: exist-body WD of `a / b` with binders `a, b Z`
fails because sibling `b > 0` is not assumed during WD (use `Z*` ratio form).
Wave3 NormalAtomic computation: `$prime` / `not $prime` / `$coprime` /
`not $coprime` on closed nonnegative integers — see
`prime_by_computation.lit`, `not_prime_by_computation.lit`,
`coprime_by_computation.lit`, `not_coprime_by_computation.lit`.
Wave5 ByDefinition builtins (no trust): `$injective` / `$surjective` /
`$bijective` (singleton identity), `$prime` (`by def $prime(5)`),
`$is_choice_function_for` (finite constant choice) — see
`atomic/by_definition/builtin_injective.lit` and siblings.
NotSubset / NotSuperset duality (A7): known `not B $superset A` proves
`not A $subset B`, and known `not B $subset A` proves `not A $superset B` —
see `not_subset_from_known_not_superset.lit`,
`not_superset_from_known_not_subset.lit`.
Subset leftovers (A8): `union(A,B) $subset union(C,D)` componentwise;
`range` / `closed_range` into `N`/`N+`/`Z`/`Q`/`R` —
see `subset_union_from_componentwise.lit`,
`subset_integer_range_numeric_carrier.lit`.
Secondary subset leaves: power-set monotone, set-minus common-right monotone,
cart componentwise, subset transitivity — see
`subset_power_set_monotone.lit`, `subset_set_minus_common_right_monotone.lit`,
`subset_cart_componentwise.lit`, `subset_transitivity.lit`.
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
B1 leftovers (verify-time only; see `order/` and `equality/`):
order-sign from literal bound; `OrderFlipMulMinusOne`;
`EqualFromKnownDifferenceZero`. Carrier → sign (`N` / `R+` / `R-` / `R*`)
moved to eager infer under `examples/infer/atomic/in_signed_standard_set_*.lit`.
Equality BuiltinRule power laws (Stage B wave 1): `a^m * a^n = a^(m+n)`,
`(a^m)^n = a^(m*n)`, `(a*b)^n = a^n * b^n`, `1/a = a^(-1)`, `a/b = a * b^(-1)`
under `examples/proof_nodes/equal/by_builtin_rule/power_*.lit` and
`reciprocal_*` / `quotient_*`.
Equality BuiltinRule identities (Stage B wave 2):
`1^a=1` (`N`), `0^n=0` (`N+`); `sqrt_*` square/zero/one/of_square/product/
quotient; `abs_*` negation/product/square; `log_*` base_self/of_one/of_power/
arg_power/product/quotient/reciprocal/change_of_base; `zero_mod`, `mod_one`,
`one_mod_at_least_two`, `nested_same_mod_absorption`.
Quotient positivity, sqrt-denominator, log-nonzero, and mod-result examples
now use checked facts. Native scalar codomains now discharge the eight equality tracers for `sign`,
`gcd`/`lcm`, `exp`, and factorial without trust or preceding carrier assertions.
See [the result-type tracer](atomic/by_builtin_rule/native_scalar_result_types.lit)
and [B01–B04 acceptance](../../plan/迁移的plan/experience/problem_notes/native-scalar-result-types.md).
Equality BuiltinRule identities (Stage B wave 3):
`min`/`max` idempotent + commutative; `abs(abs(a))=abs(a)`;
`exp(ln(x))=x` (`R+`); `ln(exp(x))=x` (`x` in `R`, with native `exp` codomain `R+`);
`floor(n)=n` / `ceil(n)=n` (`Z`); `a % a = 0` (`a != 0`) — see `min_*.lit`,
`max_*.lit`, `abs_abs_absorption.lit`, `exp_of_ln.lit`, `ln_of_exp.lit`,
`floor_of_integer.lit`, `ceil_of_integer.lit`, `mod_self_zero.lit`.
Equality BuiltinRule identities (Stage B wave 4):
`floor(ceil(n))=n`, `ceil(floor(n))=n` (`Z`); `sqrt(a^2)=abs(a)` — see
`floor_of_ceil_of_integer.lit`, `ceil_of_floor_of_integer.lit`,
`sqrt_of_square_equals_abs.lit`.
Equality BuiltinRule identities (Stage B wave 5):
`quot(a,1)=a`; `quot(a,a)=1` (`N+`); `lcm` commutative / idempotent-abs;
`gcd` commutative / idempotent-abs / left-right zero-abs (`Z*` binders for
nonzero inputs); `(n+1)!=(n+1)*n!` (native factorial codomain `N+`) — see `quot_*.lit`, `lcm_*.lit`, `gcd_*.lit`,
`factorial_successor.lit`.
Equality BuiltinRule identities (Stage B wave 6):
`abs(a)=a` (`0 <= a`); `abs(a)=0-a` (`a <= 0`); `sign(a)=1` (`0 < a`);
`sign(a)=0-1` (`a < 0`); ordered `min`/`max` — see `abs_nonneg_equals_self.lit`,
`abs_nonpos_equals_negation.lit`, `sign_of_*.lit`, `max_*_when_less_equal.lit`,
`min_*_when_less_equal.lit`.
Equality BuiltinRule identities (Stage B wave 7):
`a % gcd(a,b)=0` / `(a*b)%a=0` (nonzero divisor; native gcd codomain `N+`);
`a=b` from two-sided `<=`; `a-b=0` from `a=b`; zero-product cancel;
`sign(0-a)=0-sign(a)`; `sign(a)*abs(a)=a`; `abs(a)=sign(a)*a`;
`sign(a*b)=sign(a)*sign(b)` (native sign codomain `Z` supplies arithmetic WD);
`a=c-b` from known `a+b=c`, including `a=-b` when `c=0` — see `gcd_divides_argument.lit`,
`product_mod_factor_zero.lit`, `equality_from_two_sided_weak_order.lit`,
`diff_zero_from_equal_operands.lit`, `zero_product_cancel.lit`,
`sign_of_negation.lit`, `sign_times_abs_equals_arg.lit`,
`abs_equals_sign_times_arg.lit`, `sign_of_product.lit`,
`subtraction_from_known_addition.lit`, `additive_inverse_from_sum.lit`.

Known Or replay uses the existing structural alpha identity for nested object
binders while retaining exact free identities, conditions and carriers. See
[`set_builder_union_membership.lit`](or/by_known_or_fact/set_builder_union_membership.lit).
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
add/0 — empty-index identities are retired by WD (see `examples/wd_negative/index_*_empty_named_family.lit`); see `cot_of_half_pi.lit`,
`complex_abs_squared_of_rect_form.lit`, `exp_of_sum.lit`, `sin_of_sum.lit`,
`reduce_single_term_with_add_zero.lit`. Atomic: finite_seq finiteness —
`is_finite_set_finite_seq_zero.lit`, `is_finite_set_finite_seq_from_finite_codomain.lit`.
Empty absolute ∩ settled: no `family_intersect({})={}` (use `index_intersect`);
negative probe `examples/equal_negative/family_intersect_empty_equals_empty.lit`
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
No equality KnownRewrite slot (dead; = uses TheyAreTheSame / unified equivalence-class search).
OrderDual rewrite: `atomic/by_builtin_rewrite/order_dual*.lit`.
KnownRewrite: `atomic/by_known_rewrite/reflexivity.lit`, `symmetry.lit`.
WD negatives (must fail): `examples/wd_negative/`
(including `fn_app_not_in_function_set.lit`: `have f R` then `f(a)`).
WD gallery (positives for done Obj/Fact WD): `examples/wd/`.

## Layout

```text
or/           ByBuiltinRule (trichotomy ×3, NaturalZeroOrAtLeastOne,
              ComplementaryAtomic, AbsSignSplit, ZeroProductSplit,
              LessOrGreaterEqual, GreaterOrLessEqual, WeakOrderLeOrGe,
              EqualityPlusStrictCoversWeak, CompleteResidues,
              IntegerSuccessorTail, SquareSumComponentNonzero,
              ClassicalImplication, IntegerDiscreteSplit),
              SelectedBranch, KnownOr, KnownForall
equal/        ByTheyAreTheSame (SameIr / FnSet / AnonymousFn / SetBuilder / compound alpha),
              ByBuiltinRule (Calculation closed decimal + arithmetic_ops +
              integer_sqrt_log + complex_nested), EquivalenceClass
              (KnownPath / ViaPeers), ObjectDefinition
              (identifier / fn / template), BuiltinStrategy, MatchingOneArgByOne,
              KnownForall (+ViaSymmetry), BuiltinRewrite
              (ClosedNumericEqualSubstitution + arithmetic_ops)
atomic/       ByBuiltinRule (incl. NotIn closed/list/intersect/union/set_minus;
              NotIsFiniteSet standard infinite + set_minus; In
              union/intersect/set_minus/family_union/index_union + R-arithmetic
              closure; LessEqual abs + add/sub/mul order algebra + triangle/
              reverse-triangle/sandwich; Subset list-set/union/intersect from
              members or operand upper bounds + power-set/set-minus/cart/
              transitivity secondary leaves; Greater from known less;
              NormalAtomic `$prime`/`$coprime` + `not $prime`/`not $coprime`
              by closed-integer computation), KnownAtomicFact,
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
exist/        ByBuiltinRule (real-line, equality-from-membership, nonempty-member,
              rational Z* ratio, integer multiple from rem=0, Archimedean
              reciprocal, real density midpoint),
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
  target/release/litex -f "$f" || fail=1
done < <(find examples/proof_nodes -name '*.lit' | sort)
exit $fail
```

Equality pipeline and evidence: [step-by-step README](../../src/execute/execute_fact_stmt/verify_atomic_fact/verify_equality/README.md).

## Order and induction support

The order strategy preserves denominator-sign obligations when one comparison
side is zero, and accepts converse `>` / `>=` spellings without increasing
its recursion budget. Real-order complements cite an existing opposite fact
and include both real-carrier proofs in detailed output.

- [Quotient signs](order/quotient_nonnegative.lit)
- [Known real-order complements](order/from_known_order_complement.lit)
- [Converse structural order](order/converse_structural_order.lit)
- [Nonnegative integers as naturals](order/nonnegative_integer_carrier.lit)
- [Products of powers with natural exponents](equal/by_builtin_rule/power_product_same_base_zero_exponent.lit)
- [Iterated natural powers](equal/by_builtin_rule/power_of_power_zero_exponent.lit)
- [Natural power of a product](equal/by_builtin_rule/power_of_product_natural_exponent.lit)

These routes do not infer a negation from an unsuccessful proof search. A weak
or unknown denominator sign cannot justify division by a potentially zero value.

- [Mixed equality/order chains](chain/mixed_equality_order.lit): checked `a >= b = c >= d` stores `a >= d`; an all-equality subpath keeps equality. Opposite directions do not imply an endpoint comparison.
- [Original AM-GM proof](order/am_gm.lit): quotient sign, real-order complement, and square comparison close the original contradiction proof without trust.

Compound alpha identity is traced by
[equal/by_they_are_the_same/compound_alpha.lit](equal/by_they_are_the_same/compound_alpha.lit).
Imaginary-unit calculation is traced by
[equal/by_builtin_rule/calculation_imaginary_unit.lit](equal/by_builtin_rule/calculation_imaginary_unit.lit).
Both are strict runnable examples. Named finite-enumeration release also
checks reuse of a stored equality whose nested anonymous binder IDs differ
from the goal, retaining the original equality citation.

## Showcase local rules (2026-10-02)

These tracers require strict verification: exit 0 and top-level JSON `success: true`.

| Capability | Tracer |
| --- | --- |
| Cosine zeros from an integer offset, including general integer periods | [Cosine integer offset](equal/by_builtin_strategy/cos_zero_integer_offset.lit) |
| Native pi nonzero evidence for division WD | [Pi nonzero](atomic/by_builtin_rule/not_equal_pi_nonzero.lit) |
| Natural-power laws over the existing numeric domains | [Natural powers](equal/by_builtin_rule/natural_power_laws.lit) |
| Tuple equality with computed coordinates | [Tuple components](equal/by_builtin_strategy/tuple_component_calculation.lit) |
| Arithmetic equality with proved operand equalities | [Arithmetic congruence](equal/by_builtin_strategy/arithmetic_congruence.lit) |
| Literal tuple projection carrier, with projection and membership evidence | [Projection membership](atomic/by_builtin_strategy/literal_tuple_projection_membership.lit) |
| Full named add2 function call and explicit calculation chain | [add2 chain](equal/by_builtin_strategy/add2_calculation_chain.lit) |

Natural-power builtin premises cite known memberships; concrete zero/negative
examples explicitly establish the literal type facts first. The add2 chain keeps
its intermediate coordinate expression. A direct `add2(...)= (4,6)` without
that step is still not proved automatically. None of these examples uses trust.

Checked return-carrier/signature leaves have dedicated tracers:
`atomic/by_builtin_rule/cart_dimension_in_natural.lit`,
`atomic/by_builtin_rule/tuple_dimension_in_natural.lit`, and
`atomic/by_builtin_rule/anonymous_function_declared_signature.lit`. Their
argument/body WD must already succeed; they do not drop domain conditions or
rename free definition owners. Focused positive and negative contracts run
with `cargo test --release predicate_domain`.

## Example small repairs (2026-10-02)

`atomic/by_builtin_rule/positive_integer_in_npos.lit` preserves the integer
and strict-positivity premise certificates, includes a checked predecessor
proof, and exercises the countdown definition. Zero, negative, fractional and
missing-premise controls live in `examples/negative/example_small_repairs/`.

`equal/by_builtin_rule/anonymous_function_beta_extension.lit` migrates the
removed `$fn_eq` spelling to ordinary equality with `by fn_extension`, while
keeping the original anonymous-function beta/algebra goal. The full opaque
integral prototype remains tracked separately in the migration plan.

The broader strict tracer is `examples/example_small_repairs.lit`.

## Local legacy migration repairs

The [collected small-capability acceptance](equal/by_builtin_rule/legacy_small_capabilities.lit)
covers guarded modulo/power/sqrt leaves, trigonometric parity and shifts,
complex-coordinate identities and extensionality, finite map cardinalities,
and ordered/unordered reduction. Each `legacy_*.lit` companion preserves its
previously rejected source as comments and runs the restored statement.
The [finite function range](atomic/by_builtin_rule/function_range_finite_domain.lit)
tracer supplies the cardinality WD dependency. Executable false/domain cases
and Detailed evidence checks live in `tests/unit/execute/legacy_small_capabilities/tests.rs`;
exact binary identities and before/after runs are retained in
`proof_journals/legacy-small-capability-repairs.json`.

The collection also checks [unique preimages of a stored bijection](exist/by_builtin_rule/bijective_preimage.lit)
and [choice-function pointwise inference](../infer/atomic/choice_function_pointwise.lit).
The preimage rule retains the bijection certificate and the target's codomain
membership; surjectivity alone and witness-dependent targets are rejected.
An [arbitrary-carrier unordered fold](../wd/finite_set_fold_arbitrary_carrier.lit)
checks that explicit associativity and commutativity certificates remain usable.

The next migration batch adds dedicated tracers for
[finite Cartesian cardinality](equal/by_builtin_rule/cartesian_size.lit),
[complex modulus multiplication](equal/by_builtin_rule/complex_modulus_product.lit),
[sine difference](equal/by_builtin_rule/sin_difference.lit),
[cosine difference](equal/by_builtin_rule/cos_difference.lit),
[adjacent left-fold partition](equal/by_builtin_rule/reduce_partition.lit), and
[fresh insertion into a finite product](equal/by_builtin_rule/finite_product_fresh_insertion.lit).
`tests/unit/execute/legacy_next_capabilities/tests.rs` checks false formulas,
domains, callback restrictions, boundary/order/seed preservation, bilingual
Normal output, Detailed evidence and inherited builtin permission/depth.
The exact three-binary comparison is in
`proof_journals/legacy-next-capability-repairs.json`.

The remaining five families have dedicated tracers for
[sine quarter-turn](equal/by_builtin_rule/sin_half_pi_shift.lit),
[cosine quarter-turn](equal/by_builtin_rule/cos_half_pi_shift.lit),
[first left-fold step](equal/by_builtin_rule/reduce_first_step.lit),
[integer fold translation](equal/by_builtin_rule/reduce_translation.lit),
[stored pointwise fold congruence](equal/by_builtin_rule/reduce_pointwise.lit), and
[member removal from a finite product](equal/by_builtin_rule/finite_product_member_removal.lit).
Pointwise congruence cites an exact stored whole forall, with its binder
renaming and optional interval domain. Translation preserves index order;
first-step recurrence preserves operation argument order; member removal
requires actual membership and a checked restriction of the callback.
The updated [exact restriction tracer](equal/by_builtin_rule/finite_product_exact_restrictions.lit)
keeps the larger source domain, checks actual anonymous restrictions, and covers
fresh insertion, reversed factor order, member removal and a zero removed factor.
The exact-domain negative manifest pairs false freshness, callback/factor changes,
missing finiteness/guard coverage and the retired false short-domain membership.
Focused domain, permission and output checks live in
`tests/unit/execute/legacy_final_capabilities/tests.rs`, with before/after
receipts in `proof_journals/legacy-final-capability-repairs.json`.

The level-0 Direct route is exercised by
[`equal/direct_closed_calculation.lit`](equal/direct_closed_calculation.lit).
It covers finite enumeration without preliminary numeric memberships and exact
fraction calculations; Rust permission tests also cover failure, WD, evidence,
and the prohibition on recursive search or symbolic substitution.

## Closed elementary calculation

The [exact rational-power tracer](equal/by_builtin_rule/closed_rational_power_calculation.lit)
covers closed positive rational bases and rational exponents with exact rational
results. `exact_rational_powers` tests include the collector
`run_examples_closed_rational_power_calculation`, Direct calculation, checked
Q+/Q domain evidence, independent eval results/no stores, irrational/overflow
controls and unchanged integer-power domains. Its strict CLI gate requires
exit 0, JSON success true and no session_error.

Four dedicated tracers cover [fraction rounding and integer operands](equal/by_builtin_rule/closed_fraction_rounding_calculation.lit),
[numeric radicals](equal/by_builtin_rule/closed_radical_calculation.lit),
[complex projections/arithmetic](equal/by_builtin_rule/closed_complex_parts_calculation.lit)
and [rational logs](equal/by_builtin_rule/closed_rational_log_calculation.lit).
Their historical folder name does not change the current winning route:
closed assertions use Direct `ByClosedCalculation`, without premise search.
Each tracer also exercises exact `eval`; its source WD is checked and no fact
is stored by display evaluation. `run_examples_closed_exact_elementary_tracers`
collects these files. The [paired negatives](../negative/closed_exact_elementary_calculation/)
retain wrong answers, illegal domains, unsupported values and overflow.

The [closed-subtraction bound tracer](atomic/by_builtin_rule/closed_subtraction_bound.lit)
consumes stored numeric upper/lower bounds with exact closed offsets under the
existing builtin ceiling. `closed_subtraction_bound` tests both source/goal
orientations, rational endpoints, insufficient and invalid bounds, source
citation and read-only memory. The original Fibonacci recursive-domain tracer
is `../wd/positive_closed_decrement_recursive.lit`.


[Direct structural membership](atomic/direct_structural_membership.lit) covers
nested numeric carriers and their use in predicate WD without intermediate
assertions. Its Rust tests reject invalid domains, wrong carriers and attempts
to call SP or unfold a user function at Direct. The proof retains constructor
nodes and cited leaf types in Detailed JSON.
[Function tuple carrier after equality](equal/by_known_special_property/fn_tuple_carrier_after_equality.lit)
checks that an explicit tuple equation preserves the existing Cartesian
codomain route. Dimension-only tuple evidence remains a fallback.

## Builtin migration acceptance (2026-10-03)

[Real-bound certificates](../wd/builtin_real_bound_certificates.lit) exercise
completeness production, opaque signature WD, obtain and theorem consumption.
[Surjective](atomic/by_definition/builtin_surjective.lit) and
[choice](atomic/by_definition/builtin_choice_function.lit) definitions keep
checked universal/witness and callable-carrier evidence. Mapping publication
has separate [injective](../infer/atomic/injective_definition.lit) and
[surjective](../infer/atomic/surjective_definition.lit) consumers.
[Migration record](../../docs/audits/builtin-prop-thm-migration-2026-10-03.md)
and [journal](proof_journals/builtin-prop-thm-migration-2026-10-03.json)
retain inventories, false/domain controls and unresolved struct/finite-set cases.

[Maximum membership](atomic/by_builtin_rule/in_finite_set_max_member.lit) and
[minimum membership](atomic/by_builtin_rule/in_finite_set_min_member.lit)
use the existing finite, nonempty, real-valued WD contract. Focused
`finite_set_extrema_membership_preserves_wd_and_target` Rust controls reject
empty, infinite, non-real inputs and unrelated target sets.

[Positive common divisor bound](atomic/by_builtin_rule/less_equal_positive_common_divisor_gcd.lit)
checks positivity and both zero residues before comparing against native gcd.
The native `(0,0)` WD exclusion remains in force.

[Nested function-carrier existential replay](forall/known_exist_nested_function_alpha.lit)
reuses a whole proved forall with renamed outer, existential and nested
function binders. The `source_replay_tests` controls retain carrier, guard,
body and existential-kind boundaries and prove the citation route at Direct.

The [stored function return superset](atomic/by_known_special_property/function_return_standard_superset.lit) tracer checks R-to-C and N+-to-Z/R return lifting, followed by fresh-element finite-product insertion with an explicit member and restricted callback signature. The leaf compares all stored candidate carriers, preserves signature and alias provenance, and declines nonstandard carriers or native template/field alternatives. Tests retain narrowing, invalid domains, mixed signatures, aliases and wrong arity.

[Explicit function argument congruence](equal/by_known_forall/function_argument_congruence_explicit.lit) proves a general X/Y-carrier equality lemma and instantiates it with a function-valued argument. It needs no trust. This documents an explicit authoring route; it does not claim automatic discovery of every anonymous-function argument equality.

[Homogeneous Cartesian coordinates](atomic/by_known_special_property/homogeneous_cart_coordinate.lit) derives variable-index coordinate membership when every factor is known equal to the target carrier. It preserves the existing indexed-object WD (positive integer index within the tuple dimension), shape provenance and all factor equality proofs. It does not infer a common superset for heterogeneous factors or manufacture symbolic tuple constructors.

[Known Cartesian index upper bounds](atomic/by_known_special_property/known_cart_index_upper_bound.lit) transports a stored upper bound through a known tuple shape. It handles Cartesian aliases and guarded function codomains without opening forall search; index positivity and integrality remain separate WD obligations.

## Local finite constructors and arithmetic rules (2026-10-05)

The thirteen-rule acceptance suite retains its fifteen original capabilities:
fourteen builtin leaves and Cartesian reconstruction on the complete
set-definition route. Each
tracer retains the formerly rejected input in comments and its active strict
acceptance, with separately executed rejection controls in
`tests/unit/execute/thirteen_builtin_rules/tests.rs` and `finite_set_reindex`.

- [FiniteSetProductReindex](equal/by_builtin_rule/finite_set_product_reindex.lit)
- [FiniteSetReduceReindex](equal/by_builtin_rule/finite_set_reduce_reindex.lit)
- [FiniteSetSumDisjointUnion](equal/by_builtin_rule/finite_set_sum_disjoint_union.lit)
- [FiniteSetSumTriangle](atomic/by_builtin_rule/finite_set_sum_triangle.lit)
- [FiniteIndexUnion](atomic/by_builtin_rule/finite_index_union.lit)
- [FloorMonotone](atomic/by_builtin_rule/floor_monotone.lit)
- [CeilMonotone](atomic/by_builtin_rule/ceil_monotone.lit)
- [EuclideanRemainder](equal/by_builtin_rule/euclidean_remainder.lit)
- [FactorialDivisibility](equal/by_builtin_rule/factorial_divisibility.lit)
- [ComplexTriangle](atomic/by_builtin_rule/complex_triangle.lit)
- [ComplexReverseTriangle](atomic/by_builtin_rule/complex_reverse_triangle.lit)
- [LcmCommonMultipleBound](atomic/by_builtin_rule/lcm_common_multiple_bound.lit)
- [Cartesian reconstruction from a complete definition](equal/by_builtin_rule/cart_reconstruction.lit)
- [RangeSize](equal/by_builtin_rule/range_size.lit)
- [ClosedRangeSize](equal/by_builtin_rule/closed_range_size.lit)

Finite product and unordered-fold reindexing retain the checked bijection;
fold WD owns associativity/commutativity and the rule retains operation/seed
matches. Disjoint finite partitioning certifies each callback restriction,
with scoped pointwise evidence when needed. Finite indexed union retains both
index finiteness and the exact stored universal fibre certificate with source
IDs and alpha renamings. No wider premise search or new runtime state is used.
The targeted collector requires exit0, root success true and no session error.

[Complete Cartesian definitions](equal/by_object_definition/cart_function_set_definition.lit)
uses the ordinary object-definition owner for exact finite domains and every
factor clause. The reconstruction proof exposes this definition explicitly;
a bare reconstruction fact can succeed with an earlier stored theorem and
still fail in a cold standalone file. Coordinate images alone do not determine
an ordinary Cartesian set. The paired exact-domain negative manifest rejects
missing coordinates, changed order/length, infinite domains and diagonal sets.

[Tuple extensionality on complete domains](../stmt_nodes/release_and_expand/tuple_exact_function_extensionality.lit)
checks empty/singleton values, symbolic lengths, different return upper bounds
and set-valued coordinates through native release and selected `by thm` calls.
Wrong lengths, omitted coordinates and an infinite source domain have separate
negative controls; failed releases publish no target equality.

Nested modulus integer-multiple reduction has a dedicated
[tracer](equal/by_builtin_rule/nested_mod_integer_multiple.lit) and
[solved guard note](experience/problem_notes/nested-mod-integer-guard-2026-10-05.md).
The rule retains the actual multiplier-in-Z proof; product/modulus WD alone
does not certify divisibility. Nonzero signed integer moduli remain legal.

The factorial migration audit retains complete checked author routes for
[predecessor recurrence](equal/by_builtin_rule/factorial_predecessor_from_successor.lit)
and [divisibility after a proved positive/nonzero theorem](equal/by_builtin_rule/factorial_divisibility_from_positive.lit).
These use existing rules; the bare predecessor/nonzero short forms and the
separate monotonicity/lcm findings are classified in the
[source-owned record](../test_objs/experience/problem_notes/legacy-factorial-gcd-lcm-audit-2026-10-05.md).


## Native exp/ln/sign author proofs (2026-10-05)

Complete checked routes using current rules are retained for
[injectivity](equal/by_builtin_rule/native_exp_ln_injectivity.lit),
[exponential differences](equal/by_builtin_rule/native_exp_difference_from_sum.lit),
[logarithm products](equal/by_builtin_rule/native_ln_product_from_exp.lit),
[logarithm quotients](equal/by_builtin_rule/native_ln_quotient_from_exp.lit),
[sign zero/nonzero](equal/by_builtin_rule/sign_zero_nonzero_from_magnitude.lit),
and [sign bounds and weak order](equal/by_builtin_rule/sign_order_from_cases.lit).
Each complete file passes strict verification. The
[source-owned audit](../test_objs/experience/problem_notes/legacy-exp-sign-audit-2026-10-05.md)
classifies automatic shortcuts separately from the two unimplemented native
order/canonical-base candidates and the unresolved real-power domain.


## Principal-root nonnegative algebra and known-equality routes

[Nonnegative products and quotients](equal/by_builtin_rule/principal_root_nonnegative_algebra.lit)
allow zero factors/numerators while keeping quotient denominators positive.
The existing leaf family retains checked nonnegative or stronger positive
premises. Six focused tests cover citations, search ceilings, false targets,
illegal root inputs, and reuse; the
[solved record](experience/problem_notes/principal-root-nonnegative-algebra-2026-10-05.md)
retains the initial failed guard replacement.
[Root equal-argument author proofs](equal/by_builtin_rule/principal_root_known_equality_author_routes.lit)
and [positive integer-power author proofs](equal/by_builtin_rule/positive_integer_power_known_equality_author_routes.lit)
show complete routes using checked scalar equalities and carrier facts.
All three complete files pass strict verification.

- `atomic/by_builtin_rule/in_family_union_from_member_alpha.lit`: actual member-set and element facts prove family-union membership when nested anonymous-function binders are renamed. Free function owners, complete signatures/bodies, guards and parent WD remain exact.

- `atomic/by_builtin_rule/in_power_set_from_restricted_image.lit`: explicitly prove a restricted function image is a subset, then reuse that exact subset citation for power-set membership. Parent object WD and stored-path/alpha argument evidence remain visible; no new search permission.


## Real-domain guards for forward square-sum rules

The [guard tracer](equal/by_builtin_rule/square_sum_zero_real_guard.lit)
requires checked real membership for both bases before zero-sum elimination
or forward nonzero-sum reasoning. Complex cancellation counterexamples are
rejected; the valid complex nonzero-sum-to-component disjunction remains
available. Dedicated proof payloads and Detailed output retain actual real
membership and sum/component citations.
The [explicit nonzero OR proof](atomic/by_builtin_rule/square_sum_nonzero_from_cases.lit)
checks the original real-domain goal by ordinary cases. Both complete files
pass strict verification; the [solved record](experience/problem_notes/square-sum-real-domain-guards-2026-10-05.md)
links the negative controls and frozen verification scope.


## Explicit division/product author routes

The [complete author examples](equal/by_builtin_rule/division_product_explicit_author_routes.lit)
use existing arithmetic identities to prove and reuse both conversion directions
over R/C/Q/Z, alongside checked alias, cancellation, and cross-product examples.
The [source-owned audit note](experience/problem_notes/legacy-division-product-author-routes-2026-10-05.md)
separates optional short-form automation from the still-open composite-divisor
branch. The strict file passes; false controls reject and the valid open branch
still fails, so no new builtin capability is claimed.


## Integer singleton interval author routes

The [nine complete author proofs](equal/by_builtin_rule/integer_singleton_interval_author_routes.lit)
first publish the missing integer weak bound, then use existing known-bound
antisymmetry and reuse the original full goal. The [source-owned note](experience/problem_notes/integer-singleton-interval-author-routes-2026-10-05.md)
separates optional singleton automation from existing source-direction bridges,
real-domain false controls, and persistent-context reuse. Both legacy/current
whole strict files pass; no new builtin or recursive search is implemented.


## Zero/nonzero reflection and source evidence

The [six-forall tracer](atomic/by_builtin_rule/zero_nonzero_reflection_evidence.lit)
checks native Neg and existing Sub inverse premises, product source/factor
orientations and guarded cancellation. ProductComponentNonzero retains the
actual known source and citation in Detailed. The [two full alias proofs](atomic/by_builtin_rule/zero_alias_nonzero_author_routes.lit)
explicitly publish product!=0 before component reflection and exact reuse;
the bare alias shortcut remains optional and unimplemented. The
[source-owned note](experience/problem_notes/zero-nonzero-reflection-2026-10-05.md)
records cold versus valid prior-context reuse and excludes false old accepts.


## Factorial order and lcm input divisibility

The [factorial tracer](atomic/by_builtin_rule/factorial_monotonicity.lit)
checks weak order and strict order with the smaller natural argument positive,
including reverse-written premises and explicit positive refinement.
The [lcm tracer](equal/by_builtin_rule/lcm_input_divisibility.lit) keeps
integer/nonzero-modulus WD and allows the other input to be zero. Left/right
input leaves remain distinct. The [full author tracer](atomic/by_builtin_rule/factorial_order_author_routes.lit)
publishes an inner factorial order before the bounded outer rule, and retains
the two positive-integer spelling bridges already checkable before the shortcut.
All three whole strict files pass current and legacy. The
[source-owned record](experience/problem_notes/factorial-lcm-leaf-repair-2026-10-05.md)
separates missing leaves, optional authors, first failure phases and cold versus
valid prior-forall reuse; no recursive search or domain contract is broadened.


## Exp/ln order leaves and authored consumers

[Aggregate](atomic/by_builtin_rule/exp_ln_order.lit) retains the former exact
failures as comments and eight current strict/weak forward/reflection statements.
Independent tracers exercise ExpStrictMonotone, ExpWeakMonotone,
LnStrictMonotone, LnWeakMonotone and the four order-reflection leaves:
- [exp_strict_monotone](atomic/by_builtin_rule/exp_strict_monotone.lit)
- [exp_strict_order_reflection](atomic/by_builtin_rule/exp_strict_order_reflection.lit)
- [exp_weak_monotone](atomic/by_builtin_rule/exp_weak_monotone.lit)
- [exp_weak_order_reflection](atomic/by_builtin_rule/exp_weak_order_reflection.lit)
- [ln_strict_monotone](atomic/by_builtin_rule/ln_strict_monotone.lit)
- [ln_strict_order_reflection](atomic/by_builtin_rule/ln_strict_order_reflection.lit)
- [ln_weak_monotone](atomic/by_builtin_rule/ln_weak_monotone.lit)
- [ln_weak_order_reflection](atomic/by_builtin_rule/ln_weak_order_reflection.lit)

The [author file](atomic/by_builtin_rule/exp_ln_order_author_routes.lit) keeps
fourteen unchanged full targets and exact reuse, including strong-to-weak,
ln sign and nested exp. The [positive image carrier](../wd/ln_positive_image_carrier.lit)
passes, while the same helper's nested-ln comparison domain consumer stays
pending. [Source-owned record](experience/problem_notes/exp-ln-order-repair-2026-10-05.md)
distinguishes this WD boundary and optional shortcuts. Exp R / Ln R+ and
inherited source-premise permissions are unchanged; no full replay claim.


## Legal fixed-base bridges

[LnAsEulerLog](equal/by_builtin_rule/ln_as_euler_log.lit) and [ExpAsEulerPower](equal/by_builtin_rule/exp_as_euler_integer_power.lit) retain exact former failures as comments. Two pure typed identities keep all native/log/power guards in parent equality WD. The [author file](equal/by_builtin_rule/native_fixed_base_author_routes.lit) verifies five unchanged original targets and exact reuse: two aliases, two composite inverses and ln order through base-e log. The original fixed-base record covers integer powers. The subsequent [real-power WD extension](../wd/pow_real_domains.lit) also checks `exp(x)=e^x` for real x; individual shortcut coverage remains separate. [Source record](experience/problem_notes/fixed-base-bridge-repair-2026-10-05.md) links owner, language/Detailed and negative gates; no global search or domain expansion.


## Elementary object definitions

[Floor/ceiling bounds](atomic/by_builtin_rule/rounding_definition_bounds.lit),
[tangent](equal/by_builtin_rule/tan_quotient_definition.lit),
[cotangent](equal/by_builtin_rule/cot_quotient_definition.lit) and
[Euclidean gcd recursion](equal/by_builtin_rule/gcd_euclidean_step.lit) preserve
former direct failures as comments and now verify under their original domains.
Each mathematical rule has a separate typed leaf. The
[finite-extremum member bounds](atomic/by_builtin_rule/finite_extremum_member_bounds.lit)
reuse the existing order leaves after adding checked real codomains and a
one-edge stored-subset carrier citation. The
[source record](experience/problem_notes/obj-definition-builtin-rules-2026-10-05.md)
links strict CLI, exact negative boundaries, ten-language output and bounded
carrier/publication gates.


## Composite-divisor explicit authors

[15 same-target authors](equal/by_builtin_rule/composite_divisor_explicit_author_routes.lit) retain the exact former failed shortcut as comments and check original domains/premises/targets. An explicit whole-denominator nonzero proof makes existing rational cancellation checkable; three-factor divisors use an independently proved matching whole-product helper before source WD. Cold automatic conversion remains optional AU64. [Source record](experience/problem_notes/composite-divisor-author-routes-2026-10-05.md) keeps pending conditional nested-ln WD, mathematical false controls and expected parser rejection separate; no kernel/search/domain expansion.


## Log unit-interval order

[Strict](atomic/by_builtin_rule/log_strict_decreasing_unit_interval.lit) and [weak](atomic/by_builtin_rule/log_weak_decreasing_unit_interval.lit) tracers preserve original former cold failures as comments and now check same-base order reversal under 0<a<1 and positive real arguments. Strict is old-positive convenience; weak nearby originals also failed legacy. Each typed leaf retains four actual guards and the reversed argument comparison, including real opposite-written source citations. [Source record](experience/problem_notes/log-unit-interval-order-repair-2026-10-05.md) links L3 gates, shared exp/ln regression, explicit strong-to-weak author and still-pending nested-ln WD. Existing increasing routes and inherited ceilings are retained.


## Zero/one Cartesian functions and empty graph identity

[Empty function graph identity](equal/by_builtin_rule/empty_function_graph_identity.lit)
retains complete-domain sources for empty literal, named, aliased and flat
multi-input function graphs.
[Empty-domain function space singleton](equal/by_builtin_rule/empty_domain_function_space_singleton.lit)
checks zero cart and empty-domain FnSet/finite_seq spaces with arbitrary return
bounds, including the empty return carrier.
[Zero/one cart membership](atomic/by_builtin_rule/cart_zero_one_membership.lit)
checks default/native membership and stored one-coordinate application.
[Zero/one cart size](equal/by_builtin_rule/cart_zero_one_size.lit)
checks the empty product cardinality one and a single factor's cardinality.
Their negative manifest partners reject wrong lengths, out-of-range calls,
cart()={} and a nonempty outer curried graph equated to the empty graph.
These tracers do not certify general object application heads, full cart
definition release, retired AST deletion or the complete migration matrix.

[guarded_empty_function_domain.lit](equal/by_builtin_rule/guarded_empty_function_domain.lit)
checks a real guard-exclusion lemma before sharing the resulting absence of
complete inputs across graph, image and function-space equalities. Ordinary
empty-graph equality then transports the member to `finite_seq(R,0)`.
The accompanying guard-domain controls retain that lemma while removing or
reversing the required guard and still reject the false conclusion.

The guarded-empty tracer also constructs named functions with an empty return carrier and an independently proved empty input domain. Literal closed_range(1,0), guarded constant bodies and guarded parameter bodies share the same return-bound contract. It checks their empty graph and zero-length membership; body WD remains mandatory. Nearby negatives reject false standalone body membership, every application outside the empty domain, nonempty/missing-guard return violations, and division by zero.


## Valid-base logarithm algebra

[Product](equal/by_builtin_rule/log_product_valid_base.lit), [quotient](equal/by_builtin_rule/log_quotient_valid_base.lit), [reciprocal](equal/by_builtin_rule/log_reciprocal_valid_base.lit) and [integer argument power](equal/by_builtin_rule/log_arg_power_valid_base.lit) preserve the old exact below-one failures as comments and check positive nonunit bases. The [acceptance note](experience/problem_notes/log-algebra-valid-base-acceptance-2026-10-06.md) records real three-route guard proofs, named mandatory argument evidence, ten-language output, false/domain controls and stored-forall citations. Reverse-written positivity under integer-power log WD remains a separate pending case.


The [fresh finite-product insertion tracer](equal/by_builtin_rule/finite_product_fresh_insertion.lit) keeps the source function on its complete union domain and uses an actual union-member proof for the inserted argument. It no longer asks that source to inhabit the smaller function domain. [Branch audit evidence](experience/problem_notes/finite-product-branches-2026-10-06.md) covers member-removal multiplication including zero factors and keeps the unresolved division goal distinct from false/domain controls.
