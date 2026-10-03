# Conversation issue recheck — 2026-10-03

> Historical checkpoint. The later [current-source status update](conversation-issue-status-update-2026-10-03.md)
> supersedes its present-tense status: release now builds, but only 81/99 owning Obj files and
> 356/377 Stmt checks pass; imaginary contradiction remains unstable. The evidence below is retained.

Task: recheck every problem found in this conversation and summarize restored
and remaining behavior. Scope: diagnostics and records only. This task changed
no kernel, mathematical example, config, AST, or Env/Runtime contract.

## Baseline and acceptance limit

**Present source cannot build.** Two `cargo build --release` attempts exit 101.
`src/execute/execute_fact_stmt/verify_state.rs` has duplicate `VerifyState`
declarations and an unfinished second declaration:

```rust
pub struct VerifyState {
    level: VerifyStateLevel
    can_rewrite: bool,
}
```

The missing comma and duplicate type are one incomplete implementation boundary,
not hundreds of independent example bugs. Source changed during the scan; the
second build still failed. No refactor was repaired in this task.

All runtime results use a fixed copy of the existing successful release:
binary SHA `1b5c41a9d783edcb692f666bd8f5889bec8c9e7539325e85c5b9c313c0ae317f`.
Its stable successful build is recorded in
[the independent Obj audit](../../examples/test_objs/proof_journals/obj_audit_2026-10-03.json)
at source SHA `c9b0a740cde136b1c2e8874de22ef68649db77dc678cd371c3fc233e873d9d92`.
Current examples/std were copied into an isolated task-owned runtime. This
binary is not claimed to represent the present unfinished source.

Binary, copied source and std stayed fixed. All 516 directly captured
mathematical files still match their executed source captures. The initial
overall fixture fingerprint also included generated KB manifests; it is not
used as a mathematical-input stability claim. That collection correction is
recorded separately.

The complete [factual journal](../../examples/test_statements/proof_journals/conversation_issue_recheck_2026-10-03.json)
contains sources, commands, exit/envelope results, mappings and qualifications.

## Coverage

| Collection | Observed result |
| --- | --- |
| Current Obj inventory | 99 owning positive files pass; 524 positive IDs; all 284 rejection fixtures reject |
| Historical gaps | 72 inventoried: four positive gaps pass and unordered-subtraction negative rejects; 67 direct positives still reject |
| Original 104 Obj mismatches | All mapped: 32 requested positives pass, five bad admissions reject, 67 still reject; 29 changed/deleted sources separately replayed |
| Later 78 Obj mismatches | Now 67: ten positive recoveries and one incorrect-admission closure |
| Original Stmt snapshot | All 372 checks match recorded expectations, including the automatic K005 boundary |
| Current Stmt snapshot | 372/377 match this binary; five new compound-impossible checks require a newer successful build |
| Previously failing public files | 26/37 now match; 11 unchanged files fail, including two with checked migrations below |
| Previously failing module/cwd contexts | 22/24 first/repeated checks match; qualified arithmetic project remains rejected unchanged |
| CLI contracts | Six qualified-template and three configured-eval envelope checks pass |
| Exploratory files | Three of 18 earlier failures pass; 15 still reject, listed separately |

Counts are observations, not independent bug counts. A passing known-gap
baseline does not mean its bare assertion succeeds.

## Restored behavior on the pinned binary

| Finding | Current checked boundary |
| --- | --- |
| `0 > 0` overflow | Rejects normally; `1 > 0` passes; invalid guarded sum/fold reject without a crash |
| Aggregate callable-domain omissions | Invalid sum/product/fold domains and predicates reject; valid controls pass |
| Non-real finite extrema | `finite_set_max({i})` / `finite_set_min({i})` reject; real controls pass |
| Unordered fold accepts invalid operations | Subtraction and `2*a+b` reject; literal/named/aliased addition and multiplication pass; ordered subtraction still passes |
| Empty/nested Cartesian internal errors | `cart({}, {1})={}` and nested projection pass; alias shape remains separate |
| Foreign same-name induction overflow | Unchanged configured source passes |
| Four old slow files | Three nested-function/tuple files pass quickly; struct-alias file returns normal proof rejection instead of timing out |
| Anonymous/aliased callable membership | Literal/alias indexed-family probes and finite-index theorem release pass |
| Choice axiom release | All five original failing Stmt checks and public release pass; separate choice-definition example below still fails |
| Decimal/imaginary/sqrt controls | Decimal normalization and false inequality boundary, `i!=0`, `1/i=-i`, `sqrt(2) in R*` and sqrt quotient pass as appropriate |
| Closed aggregate routes | Both `sum(1,3,...) = 6` and `eval sum(1,3,...)` pass |
| Config/template/eval-output drift | Migrated configs reach execution; qualified-template and failed-mount JSON contracts pass |
| K005 explicit proof | Strict enumeration/obtain/contradiction/final-citation regression passes; bare automatic assertion remains an accepted limit |
| Printed trust-have | Nonstrict replay passes; strict rejection is not a display failure |

The unordered-fold WD owner now checks `unordered_fold_laws` through verified
intermediate expansions. A standalone direct nested anonymous-function
associativity assertion still rejects; closing the bad admission does not
establish unrestricted function automation.

## Checked migrations; original files remain unchanged

### Qualified imported objects

Unchanged source fails WD at `a in C`, `is_tuple(pair)` or
`is_cart(ProductSet)`. Explicit imported-definition release supplies a checked
authoring route:

```litex
release obj def gf::main::a
release obj def gf::main2::b
release obj def gf::main::pair
release obj def gf::main2::pair
release obj def gf::main::ProductSet
gf::main::a + gf::main::a = gf::main2::b
gf::main::pair[1] = 3
gf::main2::pair[1] = 8
cart_dim(gf::main::ProductSet) = 2
```

The complete original file with only these releases added passes first and
repeated configured runs, all nine statements. The
[original caller](../../examples/module_manager/import_alias_qualified_arithmetic/main.lit)
is unchanged. Category: **Litex authoring improvement / example migration**.
Changing default imported-fact publication would require separate discussion.
These four probes do not close every other qualified Obj gap automatically.

### Symbolic power/logarithm

Direct and positivity-only variants fail at the outer power's
`log(2,2^x) in Z` requirement. This checked integer-value bridge passes:

```litex
have x N
log(2, 2^x) = x
2^(log(2, 2^x)) = 2^x
```

No trust or new assumption was added. The version with an extra positivity
line also passes. Category: **Litex authoring improvement**; retain the current
supported integer-exponent domain. The
[original public file](../../examples/proof_nodes/equal/by_builtin_rule/pow_of_log_inverse.lit)
is not modified by this scan.

K005's maintained explicit proof is
[finite-negated-existence-by-contra.lit](../../examples/test_statements/boundaries/finite-negated-existence-by-contra.lit).
Its remaining automatic rejection is not an unresolved K005 bug.
Other unchanged accepted probes confirm composition with intermediate
equalities, set equality by extension, singleton-set inequality by
contradiction, common-denominator comparison, and tuple projection after an
intermediate tuple equality.

## Remaining diagnosis/implementation work

### Imaginary-number contradiction is still unstable

```litex
by contra:
    ? i != 0
    i * i = -1
    impossible i * i != 0
```

Identical fixed binary/source/cwd in fresh processes: parallel runs pass 7/12,
reject 5/12; separate serial runs pass 5/12, reject 7/12. Failure phase is
`by_contra`, without timeout/parser failure. Direct `i!=0` passes; false `i=0`
rejects. Earlier twelve-pass checkpoints did not close instability.
Classification: **behavioral implementation instability, causal mechanism
unconfirmed**; primary blocker `kernel_problem`; ownership **provisional,
diagnosing**. Compare actual closing/equality evidence from both outcomes
before proposing global ordering/state/search changes. Acceptance needs
consistent fresh serial proofs and false-goal boundaries.

### Real-bound predicates are still undefined

```litex
release thm real_least_upper_bound_exists({0}, 1)
release thm real_greatest_lower_bound_exists({0}, 0)
```

Both fail generated-conclusion WD with `undefined_predicate` for
`is_real_least_upper_bound` / `is_real_greatest_lower_bound`. All six public
upper/lower-bound files still reject. Classification: **certificate/registration
wiring gap**; blocker `kernel_problem`; ownership **provisional, diagnosing**.
Establish the intended definition and owner; unchecked replacement predicates
are not acceptance.

### Surjection-size and choice-definition consumers still reject

```litex
have A set = {1, 2}
have B set = {1}
have fn f(x A) B = 1
exist x A st {x = 1}
by def $surjective(A, B, f)
```

The unchanged size example now first fails at `by def`, before cardinality.
Do not retain the old diagnosis that only the final WD failed. A corrected
explicit claim/witness probe also failed; no successful repair is claimed.

```litex
have fn g_choice(alpha {1}) power_set({1}) = {1}
have fn f_choice(alpha {1}) {1} = 1
forall alpha {1}:
    f_choice(alpha) $in g_choice(alpha)
by def $is_choice_function_for({1}, power_set({1}), g_choice, f_choice)
```

Pointwise membership passes; `by def` rejects. The actual signature is
`g: I -> S` and `f: I -> family_union(S)`; do not reinterpret S as a different
universe parameter. Successful choice-axiom release does not close this
consumer. Normal output reports `by_def` without a decisive inner obligation.
Classification: **definition/callable evidence composition plus diagnostic
limitation**, cause not established; blocker `kernel_problem`; ownership
**provisional, diagnosing**. Trace the requirements and verify an unchanged
source or an explicit migration before calling this solved.

### Struct aliases and tuple-backed field evidence

```litex
have chosen_struct &Triple<R> = chosen
chosen_struct.first = 1
```

Typed construction passes; field equality rejects in search. Direct Point/Pair
field cases below also remain. Trace constructor/default-view/field evidence
before choosing a local repair. Classification: **representation/evidence
composition, provisional**; blocker `kernel_problem`; ownership **provisional,
diagnosing**.

The later single-field declaration in the same old fixture has a separate
boundary:

```litex
struct ScalarOps:
    add fn(x, y R) R
```

Its independent parse probe rejects with `struct definition expects at least
two fields`. This is a current representation/example mismatch, not the first
field-equality failure. Do not add a dummy field solely to pass the file.

## The 67 remaining direct Obj cases

These are requested direct routes, not 67 confirmed independent bugs or
67 mathematically unavailable results. Some have checked explicit proofs;
others need their earliest WD/calculation/evidence owner diagnosed.

| Domain | Cases | Example |
| --- | ---: | --- |
| Functions | 4 | `f(f(1))=3`, `f(2)(3)=5` |
| Exact scalar calculation/carriers | 8 | `2^(-3)=1/8`, rational extrema, `log(e,e)=1` |
| Trigonometry | 11 | `tan(pi/4)=1`, `arctan(1)=pi/4` |
| Complex coordinates/modulus | 7 | `C_abs(3+4*i)=5`, `re(i*i)=-1` |
| Sets/families/ranges | 21 | Displayed set algebra, family operators, closed ranges |
| Structs/sequences/shapes/imports | 16 | `p.x=1`, sequence literal membership, alias/qualified dimensions |

First phases: 47 `search_proof`, 19 `well_defined`, one `let`.
Full sources/diagnostics are in the journal.

| Current fixture | Phase | First failed statement |
| --- | --- | --- |
| [gaps/anonymous_fn__p06.lit](../../examples/test_objs/gaps/anonymous_fn__p06.lit) | search_proof | `fn (x R) R{x + y}(2) = 5` |
| [gaps/arccot__p02.lit](../../examples/test_objs/gaps/arccot__p02.lit) | search_proof | `arccot(1) = pi / 4` |
| [gaps/arccot__p04.lit](../../examples/test_objs/gaps/arccot__p04.lit) | search_proof | `arccot(-1) = 3 * pi / 4` |
| [gaps/arctan__p02.lit](../../examples/test_objs/gaps/arctan__p02.lit) | search_proof | `arctan(1) = pi / 4` |
| [gaps/arctan__p03.lit](../../examples/test_objs/gaps/arctan__p03.lit) | search_proof | `arctan(-1) = -pi / 4` |
| [gaps/cart__p04.lit](../../examples/test_objs/gaps/cart__p04.lit) | search_proof | `cart({1}, {2}) = {(1, 2)}` |
| [gaps/cart_dim__p04.lit](../../examples/test_objs/gaps/cart_dim__p04.lit) | well_defined | `<wd_failed>` |
| [gaps/closed_range__p04.lit](../../examples/test_objs/gaps/closed_range__p04.lit) | search_proof | `closed_range(-1, 1) = {-1, 0, 1}` |
| [gaps/complex_abs__p03.lit](../../examples/test_objs/gaps/complex_abs__p03.lit) | search_proof | `C_abs(3 + 4 * i) = 5` |
| [gaps/complex_abs__p04.lit](../../examples/test_objs/gaps/complex_abs__p04.lit) | search_proof | `C_abs(-3) = 3` |
| [gaps/complex_abs__p05.lit](../../examples/test_objs/gaps/complex_abs__p05.lit) | search_proof | `C_abs(-i) = 1` |
| [gaps/complex_abs__p06.lit](../../examples/test_objs/gaps/complex_abs__p06.lit) | search_proof | `forall z C:     C_abs(z) >= 0` |
| [gaps/cos__p04.lit](../../examples/test_objs/gaps/cos__p04.lit) | search_proof | `cos(-pi) = -1` |
| [gaps/cot__p02.lit](../../examples/test_objs/gaps/cot__p02.lit) | well_defined | `<wd_failed>` |
| [gaps/cot__p03.lit](../../examples/test_objs/gaps/cot__p03.lit) | well_defined | `<wd_failed>` |
| [gaps/family_intersect__p01.lit](../../examples/test_objs/gaps/family_intersect__p01.lit) | search_proof | `family_intersect({{1}}) = {1}` |
| [gaps/family_intersect__p02.lit](../../examples/test_objs/gaps/family_intersect__p02.lit) | well_defined | `<wd_failed>` |
| [gaps/family_intersect__p03.lit](../../examples/test_objs/gaps/family_intersect__p03.lit) | search_proof | `family_intersect({{1}, {}}) = {}` |
| [gaps/family_intersect__p04.lit](../../examples/test_objs/gaps/family_intersect__p04.lit) | let | `let …` |
| [gaps/family_union__p02.lit](../../examples/test_objs/gaps/family_union__p02.lit) | search_proof | `family_union({{1}}) = {1}` |
| [gaps/family_union__p03.lit](../../examples/test_objs/gaps/family_union__p03.lit) | well_defined | `<wd_failed>` |
| [gaps/family_union__p04.lit](../../examples/test_objs/gaps/family_union__p04.lit) | well_defined | `<wd_failed>` |
| [gaps/family_union__p05.lit](../../examples/test_objs/gaps/family_union__p05.lit) | search_proof | `U = {1, 2}` |
| [gaps/field_access__p01.lit](../../examples/test_objs/gaps/field_access__p01.lit) | search_proof | `p.x = 1` |
| [gaps/finite_seq_set__p05.lit](../../examples/test_objs/gaps/finite_seq_set__p05.lit) | search_proof | `fn (x closed_range(1, 2)) R{x} $in finite_seq(R, 2)` |
| [gaps/finite_set_max__p04.lit](../../examples/test_objs/gaps/finite_set_max__p04.lit) | search_proof | `finite_set_max({1 / 3, 1 / 2}) = 1 / 2` |
| [gaps/finite_set_min__p04.lit](../../examples/test_objs/gaps/finite_set_min__p04.lit) | search_proof | `finite_set_min({1 / 3, 1 / 2}) = 1 / 3` |
| [gaps/finite_set_size__p05.lit](../../examples/test_objs/gaps/finite_set_size__p05.lit) | well_defined | `<wd_failed>` |
| [gaps/fn_obj__p05.lit](../../examples/test_objs/gaps/fn_obj__p05.lit) | search_proof | `f(f(1)) = 3` |
| [gaps/fn_obj__p06.lit](../../examples/test_objs/gaps/fn_obj__p06.lit) | search_proof | `f(2)(3) = 5` |
| [gaps/fn_range__p02.lit](../../examples/test_objs/gaps/fn_range__p02.lit) | search_proof | `fn_range(fn (x R) R{x}) = R` |
| [gaps/identifier_with_export_file_id__p04/main.lit](../../examples/test_objs/gaps/identifier_with_export_file_id__p04/main.lit) | well_defined | `<wd_failed>` |
| [gaps/identifier_with_export_file_id__p05/main.lit](../../examples/test_objs/gaps/identifier_with_export_file_id__p05/main.lit) | well_defined | `<wd_failed>` |
| [gaps/identifier_with_mod_and_export_file_id__p04/main.lit](../../examples/test_objs/gaps/identifier_with_mod_and_export_file_id__p04/main.lit) | well_defined | `<wd_failed>` |
| [gaps/identifier_with_mod_and_export_file_id__p05/main.lit](../../examples/test_objs/gaps/identifier_with_mod_and_export_file_id__p05/main.lit) | well_defined | `<wd_failed>` |
| [gaps/imaginary_part__p04.lit](../../examples/test_objs/gaps/imaginary_part__p04.lit) | search_proof | `img(-2 - i) = -1` |
| [gaps/index_intersect__p02.lit](../../examples/test_objs/gaps/index_intersect__p02.lit) | search_proof | `index_intersect({1}, N, A) = {1}` |
| [gaps/index_union__p02.lit](../../examples/test_objs/gaps/index_union__p02.lit) | search_proof | `index_union({1}, N, A) = {1}` |
| [gaps/intersect__p01.lit](../../examples/test_objs/gaps/intersect__p01.lit) | search_proof | `intersect({1, 2}, {2, 3}) = {2}` |
| [gaps/list_set__p04.lit](../../examples/test_objs/gaps/list_set__p04.lit) | search_proof | `{1, 2} = {2, 1}` |
| [gaps/list_set__p06.lit](../../examples/test_objs/gaps/list_set__p06.lit) | well_defined | `<wd_failed>` |
| [gaps/list_set__p07.lit](../../examples/test_objs/gaps/list_set__p07.lit) | well_defined | `<wd_failed>` |
| [gaps/log__p05.lit](../../examples/test_objs/gaps/log__p05.lit) | search_proof | `log (1 / 2, 8) = -3` |
| [gaps/log__p06.lit](../../examples/test_objs/gaps/log__p06.lit) | well_defined | `<wd_failed>` |
| [gaps/max__p05.lit](../../examples/test_objs/gaps/max__p05.lit) | search_proof | `max(1 / 3, 1 / 2) = 1 / 2` |
| [gaps/min__p05.lit](../../examples/test_objs/gaps/min__p05.lit) | search_proof | `min(1 / 3, 1 / 2) = 1 / 3` |
| [gaps/obj_at_index__p04.lit](../../examples/test_objs/gaps/obj_at_index__p04.lit) | well_defined | `<wd_failed>` |
| [gaps/obj_at_index__p06.lit](../../examples/test_objs/gaps/obj_at_index__p06.lit) | search_proof | `(2 + 3, 4 * 2)[2] = 8` |
| [gaps/pow__p04.lit](../../examples/test_objs/gaps/pow__p04.lit) | search_proof | `2 ^ -3 = 1 / 8` |
| [gaps/power_set__p06.lit](../../examples/test_objs/gaps/power_set__p06.lit) | search_proof | `power_set(power_set({})) = {{}, {{}}}` |
| [gaps/range__p04.lit](../../examples/test_objs/gaps/range__p04.lit) | search_proof | `range(-2, 1) = {-2, -1, 0}` |
| [gaps/range__p06.lit](../../examples/test_objs/gaps/range__p06.lit) | search_proof | `not 3 $in range(1, 3)` |
| [gaps/real_part__p04.lit](../../examples/test_objs/gaps/real_part__p04.lit) | search_proof | `re(-2 - i) = -2` |
| [gaps/real_part__p06.lit](../../examples/test_objs/gaps/real_part__p06.lit) | search_proof | `re(i * i) = -1` |
| [gaps/seq_set__p03.lit](../../examples/test_objs/gaps/seq_set__p03.lit) | search_proof | `fn (x N+) N{x} $in seq(N)` |
| [gaps/seq_set__p04.lit](../../examples/test_objs/gaps/seq_set__p04.lit) | search_proof | `fn (x N+) R{0} $in seq(R)` |
| [gaps/set_minus__p01.lit](../../examples/test_objs/gaps/set_minus__p01.lit) | search_proof | `set_minus({1, 2}, {2}) = {1}` |
| [gaps/sin__p04.lit](../../examples/test_objs/gaps/sin__p04.lit) | search_proof | `sin(-pi / 2) = -1` |
| [gaps/standard_set_r_pos__p03.lit](../../examples/test_objs/gaps/standard_set_r_pos__p03.lit) | search_proof | `sqrt (2) $in R+` |
| [gaps/struct_obj__p01.lit](../../examples/test_objs/gaps/struct_obj__p01.lit) | search_proof | `p.x = 1` |
| [gaps/struct_obj__p02.lit](../../examples/test_objs/gaps/struct_obj__p02.lit) | search_proof | `p.second = 2` |
| [gaps/tan__p02.lit](../../examples/test_objs/gaps/tan__p02.lit) | well_defined | `<wd_failed>` |
| [gaps/tan__p03.lit](../../examples/test_objs/gaps/tan__p03.lit) | well_defined | `<wd_failed>` |
| [gaps/tan__p04.lit](../../examples/test_objs/gaps/tan__p04.lit) | well_defined | `<wd_failed>` |
| [gaps/tuple__p04.lit](../../examples/test_objs/gaps/tuple__p04.lit) | well_defined | `<wd_failed>` |
| [gaps/tuple__p06.lit](../../examples/test_objs/gaps/tuple__p06.lit) | search_proof | `(1, 2) != (2, 1)` |
| [gaps/union__p01.lit](../../examples/test_objs/gaps/union__p01.lit) | search_proof | `union({1}, {2}) = {1, 2}` |

## Other legacy observations and limits

Fifteen internal/root scratch files still fail. Many contain removed `$fn_eq`,
removed finite-set induction, old inline trust syntax, bare operator objects,
or unfinished proof bodies. They are not public regressions and are outside
the 67 direct Obj count.

| Scratch source | Phase |
| --- | --- |
| [examples/_internal/drafts/dihedral_group_isomorphism_draft.lit](../../examples/_internal/drafts/dihedral_group_isomorphism_draft.lit) | parse |
| [examples/_internal/drafts/finite_set_index_draft.lit](../../examples/_internal/drafts/finite_set_index_draft.lit) | def_thm |
| [examples/_internal/drafts/output_trace_showcase.lit](../../examples/_internal/drafts/output_trace_showcase.lit) | parse |
| [examples/_internal/regression/by_thm_anonymous_function_body_equality.lit](../../examples/_internal/regression/by_thm_anonymous_function_body_equality.lit) | def_thm |
| [examples/_internal/regression/empty_integer_interval_is_empty.lit](../../examples/_internal/regression/empty_integer_interval_is_empty.lit) | def_thm |
| [examples/_internal/regression/finite_set_induction.lit](../../examples/_internal/regression/finite_set_induction.lit) | parse |
| [examples/_internal/regression/fn_eq_implies_equality.lit](../../examples/_internal/regression/fn_eq_implies_equality.lit) | parse |
| [examples/_internal/regression/gcd_from_finite_divisors.lit](../../examples/_internal/regression/gcd_from_finite_divisors.lit) | def_thm |
| [examples/_internal/regression/generic_cart_member_coordinates.lit](../../examples/_internal/regression/generic_cart_member_coordinates.lit) | parse |
| [examples/_internal/regression/lambda_alpha_equivalence.lit](../../examples/_internal/regression/lambda_alpha_equivalence.lit) | search_proof |
| [examples/_internal/regression/named_restricted_return_set.lit](../../examples/_internal/regression/named_restricted_return_set.lit) | parse |
| [examples/_internal/regression/numeric_power_rules.lit](../../examples/_internal/regression/numeric_power_rules.lit) | search_proof |
| [examples/_internal/regression/operator_self_equality.lit](../../examples/_internal/regression/operator_self_equality.lit) | parse |
| [examples/_internal/regression/vector_space_scalar_system.lit](../../examples/_internal/regression/vector_space_scalar_system.lit) | def_struct |
| [examples/tmp_inverse_trig.lit](../../examples/tmp_inverse_trig.lit) | search_proof |

Legacy `-compact`, `-runner`, `-before` reject at launch; `try:` rejects at
parse. Current supported release CLI forms were used throughout.
Empty indexed domains and invalid anonymous return carriers correctly reject.
Historical zero-based sequences were separately replayed; current one-based
fixtures were tested through the current inventory.

The prior native `known_only` control is recorded as passing in
[its solution note](../../examples/test_statements/experience/problem_notes/known-only-control-recheck.md).
It could not be rerun because present Rust source cannot compile; ordinary CLI
citation is not a substitute for that internal-state test.

Five new compound-impossible checks in the current Stmt manifest are ahead of
the pinned parser. Record them as binary/fixture drift and recheck after a
successful current-source build, not as the original five recovered choice
regressions.

## Next acceptance

Finish the source refactor and run `cargo build --release`, then replay this
recheck before claiming the unfinished current source is accepted.
Use checked explicit proofs for authoring gaps. For kernel gaps, establish
local producer/consumer ownership and paired positive/negative gates. Global
search/state/AST changes retain their discussion/authorization boundaries.
