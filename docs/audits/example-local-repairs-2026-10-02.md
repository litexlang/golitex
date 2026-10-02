# Local example migration repairs — 2026-10-02

Task: implement clear local fixes from the example migration scan; retain concrete
remaining difficult issues. Workspace: golitex. No trust, weakened propositions,
AST fields, Runtime/Env state contracts, or broad proof-search policy changed.

## Primary tracer and completed local repairs

```litex
let bad_max = finite_set_max({i})  # baseline accepted; now rejects
let good_max = finite_set_max({1, 2})  # still accepts
```

`finite_set_min` has the same repaired boundary. The existing WD owner now checks
`S $subset R` alongside finiteness and nonemptiness. Acceptance:
[finite_extrema_real_carrier.lit](../../examples/wd/finite_extrema_real_carrier.lit),
[executable negative](../../examples/wd_negative/finite_extrema_nonreal.lit).
Failed definitions do not publish a binding; empty and infinite sets still reject.

The finite fold now checks the declared unary iterand domain and its predicates:

```litex
let bad_domain = finite_set_reduce({0, 1}, fn(x {2}) Z {x}, fn(a, b Z) Z {a + b}, 0)
let bad_predicate = finite_set_reduce({0, 1}, fn(x Z: x > 0) Z {x}, fn(a, b Z) Z {a + b}, 0)
```

Both reject in the fixed acceptance snapshot. The shared-source predicate
negative temporarily crashed; the follow-up rebuilt binary rejects it normally
as described below. Their exact pre-repair executions were not captured; the missing
requirements were established from the owner code. Valid declared domains,
predicates, named iterands and empty sets pass
[finite_set_fold_domain.lit](../../examples/wd/finite_set_fold_domain.lit).
Associativity/commutativity is explicitly **not** closed by this repair.

Ten legacy `litex.config` files had `[hierarchy]` headers. These are migrated to
the current documented imports/file-only exports model:

```text
# before
[hierarchy]
module
[export]
A = "./A"

# after
[import]
A = "./A"
[export]
explicit_export_selection = "./explicit_export_selection.lit"
main = "./main.lit"
```

Within A, `A::chap2::x` becomes owner-local `chap2::x`; the root still uses
`A::chap3::z`. The unlisted-sidecar assertion remains an executable subprocess
negative, replacing unsupported `try:`. Imported A loads before root exports,
as required by the current contract. No module-manager implementation changes
were made. Extra-file `-f scratch.lit` now passes on this version; the old README
debt was stale. All 10 configs parse, but one project has a later WD issue below.

Qualified templates now use the existing AtomicName elaborator:

```litex
\local::copied<R> = R
\Library::defs::copied<N> = N
\Library:::copied<Z> = Z
```

Previously the parser stopped at the first name and demanded `<...>` at `::`.
All forms and the old prefix example now pass. Missing templates, unknown
modules, missing arguments and overlong names reject. Acceptance:
[qualified_template_names](../../examples/module_manager/qualified_template_names/main.lit).

Configured eval failures now retain normal JSON:

```text
cd examples/module_manager/file_prefix
litex -strict -e '1 = 1'
# preceding b.lit contains 1 = 2
# before: exit 1, empty stdout
# now: exit 1, success false, session_error FailToImport, empty statement_results
```

The same mount failure is returned without executing eval code. The healthy
configured-eval control passes. Acceptance:
[eval_mount_failure](../../examples/module_manager/eval_mount_failure/main.lit).

## Latest shared-workspace checkpoint

The final `cargo build --release` succeeds. The 6 qualified-template and 3
configured-eval CLI checks also pass on the workspace binary. The primary
extrema positive/negative and valid fold pass; a wrong-domain fold rejects
normally. At that checkpoint the invalid predicate fold aborted because the
simpler `0 > 0` order goal aborted. A follow-up rebuild after a concurrent
membership-rule permission guard was added now rejects both normally;
`1 > 0` still accepts. This follow-up is not attributed to the local repairs
above and is not a whole-search termination audit. The foreign-induction crash
has meanwhile stopped reproducing. Checkpoint and follow-up observations are
preserved separately in the journal.

## Verification and attribution

- 12 focused release WD tests passed on the fixed snapshot (including 5 newly added tests).
- Six WD/corpus artifact gates met their positive/negative expectations.
- Six qualified-template subprocess checks and three eval-envelope checks passed.
- Thirty configured entrypoint checks: 28 meet expectations; two runs of the same
  qualified-arithmetic project still fail at WD. Both first-import and cached
  contexts were checked; import cache behavior preserves the remaining result.
- Full intended Obj gate: 99 objects, 473 positive assertion identifiers,
  452 process observations, **78 remaining mismatches**. These are 77 requested
  positives rejected and one invalid finite fold accepted. This is not a green
  whole-suite gate and not a count of 78 independently established bugs.

The fixed source snapshot and release binary were stable during the full Obj
run. The source/binary identities and exact commands/results are in
[the journal](../../examples/test_statements/proof_journals/example_local_repairs_2026-10-02.json).
The snapshot was used because concurrent work was changing numeric evaluation,
structs and documentation. Recoveries already present at the start are not
attributed to these repairs: decimal normalization, scalar aggregate domain
checks/calculation, function-return checks, indexed family signatures, imaginary
nonzero, empty/nested cart controls and sqrt nonzero.

## Difficult or decision-dependent remaining issues

### 1. False order goal overflow: no longer reproduces after follow-up rebuild

```litex
0 > 0
let bad = finite_set_reduce({0, 1}, fn(x Z: x > 0) Z {x}, fn(a, b Z) Z {a + b}, 0)
```

At the earlier shared-workspace checkpoint, both aborted with stack overflow,
exit -6, no JSON. The corresponding invalid finite-set sum also aborted. The
follow-up rebuilt release binary now rejects `0 > 0`, `0 $in N+`, and the
invalid guarded fold normally (exit 1, `success: false`), while `1 > 0`
accepts. The valid guarded fold and guarded function declaration passed at the
earlier checkpoint.

Source inspection identifies a recursive builtin route:
`0 > 0` → `0 $in R+` → subset-membership probes including `0 $in N+` →
the positive-integer rule requires `0 > 0` again. This is ordinary builtin
search before strategy entry. `verify_builtin_rule_premise` disables builtin
entry in the child state, but its closed-numeric exception still calls the
whole builtin dispatcher. False closed numeric membership returns `None`
and falls through into premise-producing routes. The new concurrent guard
requires `verify_state.can_use_builtin_rule` before the N+ integer/positivity
route; this cuts the identified cycle. No strategy-depth increase was made.
The original crash plus this source route and follow-up controls support the
diagnosis; a native crash backtrace was not captured. General termination
across other rule/WD/strategy boundaries remains outside this focused check.

The previously crashing foreign-induction file now accepts on this same latest
shared binary. Its earlier snapshot failure is retained in the journal, but it
is not listed as a current failure or attributed to this task's repairs.

### 2. Qualified object WD and composition

```litex
gf::main::a + gf::main::a = gf::main2::b
gf::main::pair[1] = 3
cart_dim(gf::main::ProductSet) = 2
```

All four unchanged assertions in
[import_alias_qualified_arithmetic/main.lit](../../examples/module_manager/import_alias_qualified_arithmetic/main.lit)
reject at WD after the migrated import config loads. Imported fixture exports
pass alone. First/cached runs agree. Root cause remains provisional: declaration
ownership, carrier evidence and compound lookup must be traced together. A
rendered-string alias or weakened domain would not close the identity contract.

### 3. Finite fold AC proof/evidence production

```litex
let r = finite_set_reduce({1, 2}, fn(x Z) Z {x}, fn(a, b Z) Z {a - b}, 0)
```

This invalid unordered fold is still admitted. The documented operation
contract requires commutativity and associativity. A local candidate generated
and checked the two forall laws with existing proof types, but the verifier
also rejected the legitimate addition associativity goal:

```litex
forall a, b, c Z:
    fn(x, y Z) Z {x + y}(fn(x, y Z) Z {x + y}(a, b), c) = fn(x, y Z) Z {x + y}(a, fn(x, y Z) Z {x + y}(b, c))
```

The candidate was reverted. Retained evidence includes its actual generated
law and failed proof. Next: provide a sound bounded operation-law certificate
producer and its WD consumer, handling literals/names/templates without
unrestricted search or erasing the defining evidence. Ordered `reduce` keeps
its separate noncommutative contract.

The follow-up also confirms admission of a visibly order-sensitive operation:

```litex
let r = finite_set_reduce({1, 2}, fn(x Z) Z {x}, fn(a, b Z) Z {2*a + b}, 0)
```

As a mathematical illustration (not a successful Litex evaluation claim),
folding from seed 0 in order 1,2 yields 4; order 2,1 yields 5. The subtraction
example violates the documented AC contract, but its fixed left fold happens
to be permutation-invariant; do not use subtraction as evidence of an
order-dependent left-fold result.

### 4. Symbolic logarithm WD composition

```litex
have x N
2^x $in R+
2^(log(2, 2^x)) = 2^x
```

The positive membership bridge passes; the final identity still fails at WD.
The direct and explicit positivity/order variants agree. Earliest owner is WD,
not the equality identity leaf. The failed obligation/evidence permission must
be traced before changing search policy. Cause is not yet established.

### 5. Real-bound theorem predicate ownership

```litex
release thm real_least_upper_bound_exists({0}, 1)
```

Rejects while checking its conclusion because `is_real_least_upper_bound` is
an undefined predicate. The analogous greatest-lower-bound family has the same
recorded interface concern, but this checkpoint directly reran only the upper
bound tracer. Next: settle the predicate definition/registration owner and
certificate interface; adding an unchecked declaration does not establish the
mathematical or proof contract.

### 6. Negated-existence route (K005)

```litex
forall x {0}:
    x != 1
not exist x {0} st {x = 1}
```

The universal exclusion passes; negated existence fails proof search. Next:
choose the intended bounded logical interface (universal exclusion conversion,
finite enumeration, or documented limitation), retaining its evidence. The
current owner records this as needing discussion; no general logical route was
silently added.

### 7. Struct alias construction/unfolding, plus an invalid older example

```litex
struct Triple<X set>:
    first X
    second X
    third X
# Later in the unchanged fixture:
have chosen_struct &Triple<R> = chosen
chosen_struct.first = 1
```

The typed declaration passes, but the field equality fails proof search. Later
the same old fixture declares a one-field struct; current parser requires at
least two fields. Preserve these as separate findings: the first needs the
constructor/alias/evidence path audited; the second needs intended representation
chosen, rather than a dummy field inserted solely to turn the file green.

## Old availability findings rechecked

`mul_nested_fn_app_in_c`, `fn_tuple_projection`, and
`standard_set_subset_and_fn_app_in_codomain` now pass in about 0.09–0.18 seconds
in these concurrent replay controls. `let_template_struct_aliases` now returns
its explicit failure in about 0.09 seconds; it no longer timed out in this run.
`sqrt_quotient` and `sqrt(2) $in R*` now pass.

```litex
by contra:
    ? i != 0
    i * i = -1
    impossible i * i != 0
```

This old instability tracer passed all 12 fresh processes on the fixed replay
binary. Historical instability remains unexplained; twelve passes do not
establish the old cause or justify claiming a determinism repair.

## Obj residual inventory: still needs individual classification

These unchanged direct fixtures are current mismatches, not automatically
classified as difficult repairs. Their full source and diagnostic are retained
in the journal. The corpus todo remains the source-owned investigation list.

| File | Requested / observed | First reported phase |
| --- | --- | --- |
| [examples/test_objs/gaps/fn_obj__p05.lit](../../examples/test_objs/gaps/fn_obj__p05.lit) | accept / reject | search_proof |
| [examples/test_objs/gaps/fn_obj__p06.lit](../../examples/test_objs/gaps/fn_obj__p06.lit) | accept / reject | search_proof |
| [examples/test_objs/gaps/pow__p04.lit](../../examples/test_objs/gaps/pow__p04.lit) | accept / reject | search_proof |
| [examples/test_objs/gaps/abs__p05.lit](../../examples/test_objs/gaps/abs__p05.lit) | accept / reject | search_proof |
| [examples/test_objs/gaps/min__p05.lit](../../examples/test_objs/gaps/min__p05.lit) | accept / reject | search_proof |
| [examples/test_objs/gaps/max__p05.lit](../../examples/test_objs/gaps/max__p05.lit) | accept / reject | search_proof |
| [examples/test_objs/gaps/sin__p04.lit](../../examples/test_objs/gaps/sin__p04.lit) | accept / reject | search_proof |
| [examples/test_objs/gaps/sin__p06.lit](../../examples/test_objs/gaps/sin__p06.lit) | accept / reject | search_proof |
| [examples/test_objs/gaps/cos__p04.lit](../../examples/test_objs/gaps/cos__p04.lit) | accept / reject | search_proof |
| [examples/test_objs/gaps/cos__p06.lit](../../examples/test_objs/gaps/cos__p06.lit) | accept / reject | search_proof |
| [examples/test_objs/gaps/tan__p02.lit](../../examples/test_objs/gaps/tan__p02.lit) | accept / reject | well_defined |
| [examples/test_objs/gaps/tan__p03.lit](../../examples/test_objs/gaps/tan__p03.lit) | accept / reject | well_defined |
| [examples/test_objs/gaps/tan__p04.lit](../../examples/test_objs/gaps/tan__p04.lit) | accept / reject | well_defined |
| [examples/test_objs/gaps/cot__p02.lit](../../examples/test_objs/gaps/cot__p02.lit) | accept / reject | well_defined |
| [examples/test_objs/gaps/cot__p03.lit](../../examples/test_objs/gaps/cot__p03.lit) | accept / reject | well_defined |
| [examples/test_objs/gaps/arctan__p02.lit](../../examples/test_objs/gaps/arctan__p02.lit) | accept / reject | search_proof |
| [examples/test_objs/gaps/arctan__p03.lit](../../examples/test_objs/gaps/arctan__p03.lit) | accept / reject | search_proof |
| [examples/test_objs/gaps/arccot__p02.lit](../../examples/test_objs/gaps/arccot__p02.lit) | accept / reject | search_proof |
| [examples/test_objs/gaps/arccot__p04.lit](../../examples/test_objs/gaps/arccot__p04.lit) | accept / reject | search_proof |
| [examples/test_objs/gaps/log__p05.lit](../../examples/test_objs/gaps/log__p05.lit) | accept / reject | search_proof |
| [examples/test_objs/gaps/log__p06.lit](../../examples/test_objs/gaps/log__p06.lit) | accept / reject | well_defined |
| [examples/test_objs/gaps/real_part__p04.lit](../../examples/test_objs/gaps/real_part__p04.lit) | accept / reject | search_proof |
| [examples/test_objs/gaps/real_part__p06.lit](../../examples/test_objs/gaps/real_part__p06.lit) | accept / reject | search_proof |
| [examples/test_objs/gaps/imaginary_part__p04.lit](../../examples/test_objs/gaps/imaginary_part__p04.lit) | accept / reject | search_proof |
| [examples/test_objs/gaps/complex_abs__p03.lit](../../examples/test_objs/gaps/complex_abs__p03.lit) | accept / reject | search_proof |
| [examples/test_objs/gaps/complex_abs__p04.lit](../../examples/test_objs/gaps/complex_abs__p04.lit) | accept / reject | search_proof |
| [examples/test_objs/gaps/complex_abs__p05.lit](../../examples/test_objs/gaps/complex_abs__p05.lit) | accept / reject | search_proof |
| [examples/test_objs/gaps/complex_abs__p06.lit](../../examples/test_objs/gaps/complex_abs__p06.lit) | accept / reject | search_proof |
| [examples/test_objs/gaps/union__p01.lit](../../examples/test_objs/gaps/union__p01.lit) | accept / reject | search_proof |
| [examples/test_objs/gaps/intersect__p01.lit](../../examples/test_objs/gaps/intersect__p01.lit) | accept / reject | search_proof |
| [examples/test_objs/gaps/set_minus__p01.lit](../../examples/test_objs/gaps/set_minus__p01.lit) | accept / reject | search_proof |
| [examples/test_objs/gaps/family_union__p02.lit](../../examples/test_objs/gaps/family_union__p02.lit) | accept / reject | search_proof |
| [examples/test_objs/gaps/family_union__p03.lit](../../examples/test_objs/gaps/family_union__p03.lit) | accept / reject | well_defined |
| [examples/test_objs/gaps/family_union__p04.lit](../../examples/test_objs/gaps/family_union__p04.lit) | accept / reject | well_defined |
| [examples/test_objs/gaps/family_union__p05.lit](../../examples/test_objs/gaps/family_union__p05.lit) | accept / reject | search_proof |
| [examples/test_objs/gaps/family_intersect__p01.lit](../../examples/test_objs/gaps/family_intersect__p01.lit) | accept / reject | search_proof |
| [examples/test_objs/gaps/family_intersect__p02.lit](../../examples/test_objs/gaps/family_intersect__p02.lit) | accept / reject | well_defined |
| [examples/test_objs/gaps/family_intersect__p03.lit](../../examples/test_objs/gaps/family_intersect__p03.lit) | accept / reject | search_proof |
| [examples/test_objs/gaps/family_intersect__p04.lit](../../examples/test_objs/gaps/family_intersect__p04.lit) | accept / reject | let |
| [examples/test_objs/gaps/power_set__p06.lit](../../examples/test_objs/gaps/power_set__p06.lit) | accept / reject | search_proof |
| [examples/test_objs/gaps/index_union__p02.lit](../../examples/test_objs/gaps/index_union__p02.lit) | accept / reject | search_proof |
| [examples/test_objs/gaps/index_intersect__p02.lit](../../examples/test_objs/gaps/index_intersect__p02.lit) | accept / reject | search_proof |
| [examples/test_objs/gaps/list_set__p04.lit](../../examples/test_objs/gaps/list_set__p04.lit) | accept / reject | search_proof |
| [examples/test_objs/gaps/list_set__p06.lit](../../examples/test_objs/gaps/list_set__p06.lit) | accept / reject | well_defined |
| [examples/test_objs/gaps/list_set__p07.lit](../../examples/test_objs/gaps/list_set__p07.lit) | accept / reject | well_defined |
| [examples/test_objs/gaps/range__p04.lit](../../examples/test_objs/gaps/range__p04.lit) | accept / reject | search_proof |
| [examples/test_objs/gaps/range__p06.lit](../../examples/test_objs/gaps/range__p06.lit) | accept / reject | search_proof |
| [examples/test_objs/gaps/closed_range__p04.lit](../../examples/test_objs/gaps/closed_range__p04.lit) | accept / reject | search_proof |
| [examples/test_objs/gaps/finite_seq_set__p05.lit](../../examples/test_objs/gaps/finite_seq_set__p05.lit) | accept / reject | search_proof |
| [examples/test_objs/gaps/seq_set__p03.lit](../../examples/test_objs/gaps/seq_set__p03.lit) | accept / reject | search_proof |
| [examples/test_objs/gaps/seq_set__p04.lit](../../examples/test_objs/gaps/seq_set__p04.lit) | accept / reject | search_proof |
| [examples/test_objs/gaps/cart__p04.lit](../../examples/test_objs/gaps/cart__p04.lit) | accept / reject | search_proof |
| [examples/test_objs/gaps/tuple__p04.lit](../../examples/test_objs/gaps/tuple__p04.lit) | accept / reject | well_defined |
| [examples/test_objs/gaps/tuple__p06.lit](../../examples/test_objs/gaps/tuple__p06.lit) | accept / reject | search_proof |
| [examples/test_objs/gaps/cart_dim__p04.lit](../../examples/test_objs/gaps/cart_dim__p04.lit) | accept / reject | well_defined |
| [examples/test_objs/gaps/obj_at_index__p04.lit](../../examples/test_objs/gaps/obj_at_index__p04.lit) | accept / reject | well_defined |
| [examples/test_objs/gaps/obj_at_index__p06.lit](../../examples/test_objs/gaps/obj_at_index__p06.lit) | accept / reject | search_proof |
| [examples/test_objs/gaps/anonymous_fn__p06.lit](../../examples/test_objs/gaps/anonymous_fn__p06.lit) | accept / reject | search_proof |
| [examples/test_objs/gaps/fn_range__p02.lit](../../examples/test_objs/gaps/fn_range__p02.lit) | accept / reject | search_proof |
| [examples/test_objs/gaps/reduce__p03.lit](../../examples/test_objs/gaps/reduce__p03.lit) | accept / reject | search_proof |
| [examples/test_objs/gaps/reduce__p04.lit](../../examples/test_objs/gaps/reduce__p04.lit) | accept / reject | search_proof |
| [examples/test_objs/gaps/reduce__p05.lit](../../examples/test_objs/gaps/reduce__p05.lit) | accept / reject | search_proof |
| [examples/test_objs/negative/finite_set_reduce__n01.lit](../../examples/test_objs/negative/finite_set_reduce__n01.lit) | reject / accept | success |
| [examples/test_objs/gaps/finite_set_reduce__p02.lit](../../examples/test_objs/gaps/finite_set_reduce__p02.lit) | accept / reject | search_proof |
| [examples/test_objs/gaps/finite_set_reduce__p03.lit](../../examples/test_objs/gaps/finite_set_reduce__p03.lit) | accept / reject | search_proof |
| [examples/test_objs/gaps/finite_set_reduce__p04.lit](../../examples/test_objs/gaps/finite_set_reduce__p04.lit) | accept / reject | search_proof |
| [examples/test_objs/gaps/finite_set_reduce__p05.lit](../../examples/test_objs/gaps/finite_set_reduce__p05.lit) | accept / reject | search_proof |
| [examples/test_objs/gaps/finite_set_size__p05.lit](../../examples/test_objs/gaps/finite_set_size__p05.lit) | accept / reject | well_defined |
| [examples/test_objs/gaps/finite_set_max__p04.lit](../../examples/test_objs/gaps/finite_set_max__p04.lit) | accept / reject | search_proof |
| [examples/test_objs/gaps/finite_set_min__p04.lit](../../examples/test_objs/gaps/finite_set_min__p04.lit) | accept / reject | search_proof |
| [examples/test_objs/gaps/struct_obj__p01.lit](../../examples/test_objs/gaps/struct_obj__p01.lit) | accept / reject | search_proof |
| [examples/test_objs/gaps/struct_obj__p02.lit](../../examples/test_objs/gaps/struct_obj__p02.lit) | accept / reject | search_proof |
| [examples/test_objs/gaps/field_access__p01.lit](../../examples/test_objs/gaps/field_access__p01.lit) | accept / reject | search_proof |
| [examples/test_objs/gaps/standard_set_r_pos__p03.lit](../../examples/test_objs/gaps/standard_set_r_pos__p03.lit) | accept / reject | search_proof |
| [examples/test_objs/gaps/identifier_with_export_file_id__p04/main.lit](../../examples/test_objs/gaps/identifier_with_export_file_id__p04/main.lit) | accept / reject | well_defined |
| [examples/test_objs/gaps/identifier_with_export_file_id__p05/main.lit](../../examples/test_objs/gaps/identifier_with_export_file_id__p05/main.lit) | accept / reject | well_defined |
| [examples/test_objs/gaps/identifier_with_mod_and_export_file_id__p04/main.lit](../../examples/test_objs/gaps/identifier_with_mod_and_export_file_id__p04/main.lit) | accept / reject | well_defined |
| [examples/test_objs/gaps/identifier_with_mod_and_export_file_id__p05/main.lit](../../examples/test_objs/gaps/identifier_with_mod_and_export_file_id__p05/main.lit) | accept / reject | well_defined |
