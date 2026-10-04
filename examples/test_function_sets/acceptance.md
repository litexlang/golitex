# Function-set composition: observed behavior on 2026-10-04

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
