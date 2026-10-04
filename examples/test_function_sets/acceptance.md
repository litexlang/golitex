# Explicit proof contract on 2026-10-04

The user clarified that explicit equalities should select the intended proof
route. A rejected direct assertion alone is not a request to broaden automatic
search. This follow-up changes only proof fixtures and records, with no kernel,
AST, state, search-policy or trust changes. Strict current release observations
are in [explicit_proofs_2026-10-04.json](explicit_proofs_2026-10-04.json); exact
source-order attempts and the nine-case baseline are in
[proof_journals/explicit_bridges_2026-10-04.json](proof_journals/explicit_bridges_2026-10-04.json).

## The user's template alias chain passes

```litex
template<a R>:
    have fn shift(x R) R = x + a
let shift_two = \shift<2>
shift_two(3) = \shift<2>(3) = 5
```

P01 preserves the alias and the final value. P03 likewise verifies
`add_two(3) = add(2)(3) = 5` after binding the returned closure. N22/N24
reject false values after both setup declarations succeed.

## A struct call needs a declared field view as well as equality

The user's exact sequence `\box<2> = (step, 0)` followed by
`\box<2>.op(3) = step(3) = 4` still rejects at **well_defined** with
`object has no definition-time struct carrier for field 'op'`. Adding
`\box<2>.op = step` also fails at that same boundary. No numeric search is
reached for the selected field. The executed current route is P02:

```litex
struct Box:
    op fn(x R) R
    tag N
have fn step(x R) R = x + 1
template<a R>:
    have box &Box = (step, 0)
\box<2> = (step, 0)
have selected &Box = \box<2>
selected.op = step
selected.op(3) = step(3) = 4
```

The typed binding provides the current declaration-owned field view; the tuple
and field equations expose the callable value. Removing the tuple equation
was tested and the field equation/call then fails search_proof. P06 verifies
the analogous sequence for `make(2)`. These are checked authoring routes for
the same returned value; they do not make the original immediate field syntax
well-defined. N23 rejects an incorrect final value after all six setup
statements succeed.

## Explicit routes for all nine retained probes

| Original direct probe | Observed phase | Checked alternative |
| --- | --- | --- |
| T05 specialized callable alias | search_proof | P01: explicit specialized call in the equality chain |
| H05 returned-function binding | search_proof | P03: explicit curried call in the equality chain |
| S02 concrete anonymous function field | search_proof | P04: field equation then anonymous call chain |
| T03 selected function-space binding | have_equal | P05: specialized carrier equation before binding |
| D05 selected function-space membership | search_proof | P05: same carrier equation before membership |
| D08 selected struct field | well_defined | P02: tuple equation, typed local binding, field equation |
| D09 returned struct field | well_defined | P06: same steps for the returned value, including result membership |
| S07 closure-valued struct template | def_template | P07: checked general tuple constructor rule, then explicit result route |
| S08 closure-valued struct return | have_fn_equal/body_in_return_set | P08: same constructor rule and returned-value route |

P07/P08 first verify this ordinary universal fact, without trust:

```litex
forall f fn(x R) R:
    (f, 0) $in &Box
```

The original closure-specific universal claim was redundant after that general
fact and was removed from the final fixtures. The template/function definitions
retain `(fn(x R) R {x + a}, 0)` and carrier `&Box`. N25 changes the tag to -1
and rejects the template definition; the general constructor fact does not
admit an invalid field value. This demonstrates a working proof interface,
without claiming the original closure-specific forall matching was repaired.

The complete audit matches 73/82 expectations: all eight new positive routes
and all 25 negatives behave as expected; nine original direct positives remain
rejected. Each accepted fixture has a clean strict-file gate in addition to
its discarded-sketch session probe. Original direct probes remain unchanged,
so the runner's exit 1 continues to report their capability boundary. These
results are not nine open kernel repair obligations.

---

# Function-body evaluation enhancement on 2026-10-04

User-authorized local kernel repair after the initial fn-set audit. The
current strict release receipt is [numeric_evaluation_2026-10-04.json](numeric_evaluation_2026-10-04.json);
[numeric_evaluation_before_2026-10-04.json](numeric_evaluation_before_2026-10-04.json)
is the immediate pre-repair baseline. Both record source, binary and fixture
identity. The original failures below remain historical evidence.

## Direct acceptance

The exact requested code now verifies without intermediate equalities:

```litex
have fn add(x R) fn(y R) R = fn(y R) R {x + y}
add(2) $in fn(y R) R
add(2)(3) $in R
add(2)(3) = 5
add(1 / 3)(1 / 6) = 1 / 2
add(0.1)(0.2) = 0.3
```

Active file: `numeric_evaluation/e01.lit`. The formerly rejected direct H01
is unchanged. H03/H04/H06–H11, T04 and T07 also now verify: anonymous and
three-level closures, named function returns, higher-order apply/composition,
inner and outer guards, and direct template applications. This fixes eleven
old positive goals. Previously accepted positives remain accepted; D01–D04
still check their explicit equality chains. E02 adds arithmetic expressions
with nested known calls inside a function body.

All 21 CLI negatives reject at their expected phase after successful setup.
In particular, N11–N14 preserve carriers/arity/guards, N17 rejects the result
6, and N21 rejects the nearby decimal 0.500000000001 for the exact fraction
1/2. The current full corpus accepts 40/49 positives and matches 61/70 total
expectations. Its exit 1 is solely the nine retained intended positives:
T03, T05, S02, S07, S08, H05, D05, D08 and D09.

## Mechanism and boundary

`normalize_function_body.rs` consumes curried argument groups in order,
substitutes a known anonymous body, and continues the returned application.
It also substitutes known calls in arguments and arithmetic children. Each
step retains the callable application's WD, the chosen body source (stored
equality path or specialized template definition), that body's own signature
and guard WD, the substituted body, and the continued application. The final
residual equality uses the existing restricted verifier and exact arithmetic.
For add(2)(3), the two body steps end at 2+3; the residual proves 2+3=5.

A checked single-step beta equality whose body exactly matches the target
is retained before deeper substitution, preserving explicit symbolic body
equations. The local route stops at a repeated active function head, 64 substitutions,
or recursion depth 64. It expands mathematical function bodies only; it does
not execute algorithms or change global proof-search permission levels. The
shared single-beta helper and its aggregate/builtin consumers are unchanged.
Detailed JSON now owns `normalization.expansions` in the named/template
function-definition route; each known source contains `function_equal` and
its citations. The existing displayed `expanded_body` and residual proof
remain available. Typed evidence retains anonymous binder environments.

Ten focused Rust tests check positive values, detailed evidence, nearest
negative boundaries, a broader name signature with a guarded selected body,
cyclic body equations, budget exhaustion, ignored legal arguments and subsequent session usability.
The existing shared-level test now accepts the approved top-level
wrapped(3)=4 calculation, while separately rejecting it under the strategy's
restricted child state. This changes the numeric acceptance oracle without
changing VerifyState or the search-stage schedule.

Focused release gates are listed in [numeric_evaluation_tests.json](numeric_evaluation_tests.json).
Source-order before/after discarded strict REPL probes are in
[proof_journals/numeric_evaluation_2026-10-04.json](proof_journals/numeric_evaluation_2026-10-04.json).
No trust, protected AST/state change, full examples/docs/textbook gate, Lean
compilation or display-eval claim is included in this scoped acceptance.

---

# Initial function-set composition audit on 2026-10-04

Task: the user's requested audit of function sets, templates, struct functions
and functions returning functions. All snippets below point to executed
fixtures. Source, binary and fixture hashes are in `audit_2026-10-04.json`.
No language or kernel behavior was changed by this task.

## Primary tracer: function-valued return

The declaration and both application carriers work. Direct numeric evaluation
does not close, but the following explicit proof does:

```litex
# Direct assertion in higher_order/h01.lit: rejected at search_proof.
# have fn add(x R) fn(y R) R = fn(y R) R {x + y}
# add(2)(3) = 5

# Active checked proof in controls/d02.lit:
have fn add(x R) fn(y R) R = fn(y R) R {x + y}
add(2) = fn(y R) R {2 + y}
add(2)(3) = fn(y R) R {2 + y}(3) = 5
```

`higher_order/h02.lit` separately verifies `add(2) $in fn(y R) R` and
`add(2)(3) $in R`. `N11`–`N15` retain the inner argument, arity, guard, outer
guard and returned-codomain boundaries; `N17` rejects the false value `6`.
`controls/d03.lit` also verifies an extracted returned closure after its body
equation is known. Parentheses around an anonymous function's nested return
carrier disambiguate which `{body}` belongs to which function; D10 and D11
verify anonymous and three-level typing with that syntax.

The relevant current implementation is
`src/execute/execute_fact_stmt/verify_atomic_fact/verify_equality/by_object_definition/by_fn_application/by_have_fn_equal.rs`:

```rust
if fn_obj.body.len() != 1 {
    return Ok(None);
}
```

This rules out that direct multi-application unfolding route. It does not show
that higher-order mathematics is impossible, or establish that implicit
recursive evaluation is the intended kernel contract. H06/T04 likewise reject
a direct higher-order application value, while D01/D04 pass this proof shape:

```litex
have fn apply(g fn(x R) R, a R) R = g(a)
have fn step(x R) R = x + 1
apply(step, 2) = step(2) = 3
```

## Template carriers and callable specialization

T01/T02/T06/T08 pass: generic identity, separate value specializations,
preserved guards, and function-valued return carriers. T05 has a different
failure from numeric unfolding:

```litex
template<a R>:
    have fn shift(x R) R = x + a
let shift_two = \shift<2>
shift_two(3) = 5
```

The first two statements pass; the call fails WD with
`no matching function signature`. Direct `\shift<2>(3) = 5` passes in T02.
Ordinary function aliases pass B04, and callable field aliases pass S04.
No working alias correction was established in this audit.

A template-selected function set needs an explicit equality in these probes.
T03 fails to bind a function using that carrier, and D05's direct membership
fails. D12 checks the same carrier with a verified equality bridge:

```litex
template<A, B nonempty_set>:
    have maps set = fn(x A) B
\maps<R, Z> = fn(x R) Z
fn(x R) Z {0} $in \maps<R, Z>
have f \maps<R, Z> = fn(x R) Z {0}
f(2) = 0
```

This is an observed authoring route. It does not silently change T03/D05 into
passing direct assertions. Template parameter-dependent families remain
distinct from forbidden parameter-dependent function signatures (N18–N20).

## Struct function fields and returned struct views

S01/S03–S06/S09 pass: parameter substitution, struct laws, callable aliases,
nested field paths, a field returning a function, and a function field whose
domain is an earlier field. D06/D07 check a constructed struct using an
existing named function, including this exact evaluated result:

```litex
struct Box:
    op fn(x R) R
    tag N
have fn step(x R) R = x + 1
have box &Box = (step, 0)
box.op = step
box.op(2) = step(2) = 3
```

S02 proves the anonymous field's function-set membership before constructing
its tuple-backed struct; construction succeeds and direct field evaluation
still fails. This avoids confusing a missing field-carrier premise with the
later evaluation boundary.

D08/D09 successfully define a template-selected struct and a function that
returns a struct, but their immediate callable fields fail WD:

```litex
# D08, after Box and step are defined:
template<a R>:
    have box &Box = (step, 0)
\box<2>.op(3) = 4

# D09, in an independent fixture with the same Box and step definitions:
have fn make(a R) &Box = (step, 0)
make(2).op(3) $in R
```

Both report `object has no definition-time struct carrier for field 'op'`.
D13/D14 show a checked typing bridge, without adding trust:

```litex
# D13, after the same template definition:
have selected &Box = \box<2>
selected.op(3) $in R

# D14, after the same make definition:
have selected &Box = make(2)
selected.op(3) $in R
```

The current owner `resolve_definition_struct_carrier` in
`src/execute/execute_fact_stmt/well_defined_results/verify_obj/structs.rs`
reads the exact object's stored view or walks an existing field path; it does
not derive the receiver's view from a template's selected type or a function's
declared return carrier. The parser admits these paths but WD rejects them.

S07/S08 expose an earlier issue: even after a successful checked universal
tuple-membership claim, a template/function returning a struct that contains
an anonymous closure fails definition checking. S07 reports only
`def_template`; S08 identifies `body_in_return_set` and the tuple's struct
membership. These are retained investigations, not established consequences
of the later view-resolution failure.

## Gates and limits

The 67 clean strict CLI fixtures produce 27 accepted positives, 20 rejected
positive goals and 20 correctly rejected negatives. The suite intentionally
returns exit 1 until every positive goal is accepted. No unexpected acceptance,
timeout, crash or protocol failure occurred in the final receipt.

The following focused Rust commands pass **23 actual tests** (5 + 6 + 10 + 2):

```sh
cargo test --release struct_field_instantiation_tests -- --nocapture
cargo test --release function_signature_scope_tests -- --nocapture
cargo test --release execute_def_template_stmt::tests -- --nocapture
cargo test --release function_application_wd_evidence_tests -- --nocapture
```

Three existing strict CLI tracers pass: `template_definition_facts.lit`,
`struct_field_instantiation.lit`, and `fixed_function_signature_scopes.lit`.
The existing `examples/test_objs/fn_set.lit` fails at line 22:

```litex
let F = fn(x R) x
```

Its P04 still uses the now-forbidden parameter-dependent return carrier; the
current fixed-signature tests deliberately reject that shape. This is fixture
drift, not evidence that the signature restriction is broken. The old fixture
was left unchanged during this scoped audit.

The final corpus gate and existing gates share a stable source/binary identity.
One intermediate build was discarded because another task changed source
during it. Earlier journal attempts retain their evidence separately; final
claims rely on the dated clean-file receipt. Broader examples, documentation,
textbooks, extracted programs and Lean gates were not run.
