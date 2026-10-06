# Object definition and carrier lookup clarification

Task: user confirms every object satisfies is_set and asks whether the ten retained function-set probes all fail because function lookup misses the corresponding definition.
Date: 2026-10-06. Scope: contract correction and source inspection; no Rust changes or new ten-probe runtime certification. Probe results and successful explicit routes remain the named Oct5 frozen-binary observations.

## PowerSet input question closed by user-owned semantics

The user explicitly confirms that all well-defined Litex objects are sets. This agrees with `search_is_set_fact_proof_by_builtin_rule`: its documented contract is “every well-defined object is a set”, and it returns the existing is_set proof for every parameter already admitted by WD.

```litex
$is_set(1)
template<a power_set(1)>:
    have item R = 0
```

The template's observed acceptance is legitimate under this contract. Adding an is_set premise would not reject 1. The previous “PowerSet input domain pending” diagnosis imported an unconfirmed distinction between numbers and sets; remove it from active todos. No verifier repair or rejection control is requested. Historical CLI receipts remain unchanged.

## Common direction, distinct owners

These probes share a high-level theme: declared/defined information is not followed through a composed expression into the consumer. They do not all reduce to finding a named function body.

| Cases | Information needed | Earliest recorded boundary |
| --- | --- | --- |
| T03 / D05 | Expand a template-produced set to its function-space value | have_equal / search_proof |
| T05 / H05 / S02 | Follow an alias or field value to a callable definition and check its application | search_proof |
| S07 / S08 / D08 / D09 / FIELD_PREMISES | Resolve the template/application receiver's declared struct view, then its field type | WD, before numeric/value proof search |

T03/D05 are object/carrier definition consumption:

```litex
\maps<R, Z> = fn(x R) Z
fn(x R) Z {0} $in \maps<R, Z>
```

The already checked value bridges include:

```litex
shift_two(3) = \shift<2>(3) = 5
add_two(3) = add(2)(3) = 5
box.op = fn(x R) R {x + 1}
box.op(2) = fn(x R) R {x + 1}(2) = 3
```

The equality object-definition dispatcher matches the current expression/head shape: Identifier has object-definition branches; named FnObj applications have function-definition branches; template heads have template branches. This supports a definition-composition/alias explanation; it does not establish that the underlying declaration itself is absent. Automatic composition is not restored by this documentation update.

For fields, the inspected owner `verify_obj/structs.rs::resolve_definition_struct_carrier` first looks for `DefaultStructView` under the exact object's IR in visible execution environments. It then handles nested FieldAccess. Other receiver shapes return None unless they already have that exact view. `verify_field_access_obj_well_definedness` reports the missing definition-time carrier before field-headed function application can collect its function signature.

```litex
# Recorded direct WD miss:
make(2).op(3) $in R

# Already checked D09 interface:
make(2) = (step, 0)
have selected &Box = make(2)
selected.op = step
selected.op(3) = step(3) = 4
selected.op(3) $in R
```

Thus a general investigation should distinguish two consumers: retrieving checked definition/value information, and retrieving a declared struct carrier plus field signature. A shared definition-tracing facility may be relevant, but no implementation/interface is decided here. Increasing function-body search depth alone does not pass the field WD gate. The typed local object gives the current owner an explicit definition-selected view; it does not make the direct receiver syntax legal.

Old closure-specific definition failures in S07/S08 are historical: the Oct5 receipt shows their setup definitions succeeding and the later field WD failing. Do not revive those old definition failures as current blockers.

Sources: `src/execute/execute_fact_stmt/well_defined_results/verify_obj/structs.rs`, `core.rs`; `verify_equality/by_object_definition/search_equal_fact_proof_by_object_definition.rs`; existing positive counterparts and `plan/迁移的plan/proof_journals/example-remaining-context-gates-2026-10-05.json`.

Completed task protocol: inspect exact current source owners and historical probe/counterpart evidence; record the confirmed PowerSet semantics; remove its stale pending item; update the canonical plan and source todo; check the documentation diff. No AST, Env/Runtime, Rust or .lit changes, no new execution or acceptance claim.
