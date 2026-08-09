# To-Lean Implementation Status

Last updated: 2026-08-09

This file is the implementation ledger for the current To-Lean work. The
inventory is authoritative for rule-by-rule coverage; this page tracks the
pipeline and delivery checkpoints.

## Pipeline completeness

- [x] Strict fail-closed APIs remain available.
- [x] Report APIs return `Complete` or `Incomplete` in the value.
- [x] Unsupported IR construction and Lean emission are distinguished.
- [x] Every omission records statement index, rendered statement, source path,
  line, phase, and reason.
- [x] Lean emission rolls back atomically per source statement.
- [x] Generated partial Lean contains omission comments and no implicit
  `axiom` or `sorry`.
- [x] The partial tracer passes Litex, focused Rust, rollback, and real Lean
  kernel gates.

Tracer:
[`examples/05_compiler_interop/to_lean_partial_report.lit`](../../examples/05_compiler_interop/to_lean_partial_report.lit)

## Builtin rule inventory

- [x] Generate and audit the complete source-derived builtin rule inventory.
- [x] Record each rule's owning Rust file and checked Lean tactic/lemma mapping.
- [x] Mark evaluation/computation-like rules as `not_this_round`.

Current source audit: 460 direct success-constructor calls expand through
forwarding helpers to 656 label-bearing sites (630 rules and 26 strategies),
including 560 distinct static labels and 73 dynamic label expressions. There
are 46 evaluation/computation-like sites marked `not_this_round`.
The checked mapping count is now 23 sites: the prior normalization and
quotient-nonzero sites plus the 20-rule tranche below.

Inventory:
[`builtin_rule_inventory.md`](builtin_rule_inventory.md)

## Structured builtin implementations

- [x] Quotient nonzero (`div_ne_zero`, including reversed orientation).
- [x] Select 20 representative non-evaluation builtin rules from the audited
  inventory.
- [x] Implement typed verifier evidence, compiler IR, checked Lean lowering,
  malformed-certificate regressions, and one persistent 20-rule tracer.

| Typed rule | Verifier contract | Checked Lean lowering |
| --- | --- | --- |
| `LessEqualFromStrictOrder` | `<` to `<=` | `linarith only` |
| `GreaterEqualFromStrictOrder` | `>` to `>=` | `linarith only` |
| `SubNonnegativeFromLessEqual` | `v <= u` to `0 <= u - v` | `linarith only` |
| `SubPositiveFromLess` | `v < u` to `0 < u - v` | `linarith only` |
| `AddNonnegative` | nonnegative summands | `linarith only` |
| `AddPositive` | positive summands | `linarith only` |
| `AddPositiveLeftStrict` | positive + nonnegative | `linarith only` |
| `AddPositiveRightStrict` | nonnegative + positive | `linarith only` |
| `MulNonnegative` | nonnegative factors | `mul_nonneg` |
| `MulPositive` | positive factors | `mul_pos` |
| `DivNonnegative` | nonnegative numerator, positive denominator | `div_nonneg` + `le_of_lt` |
| `DivPositive` | positive numerator and denominator | `div_pos` |
| `AddCommonLeftLessEqual` | add common left term to `<=` | `linarith only` |
| `SubRightNonnegativeLessEqual` | subtract nonnegative right term from `<=` | `linarith only` |
| `AddRightNonnegativeLessEqual` | add a nonnegative right term | `linarith only` |
| `AddComponentwiseLessEqual` | componentwise `<=` addition | `linarith only` |
| `AddCommonLeftLess` | add common left term to `<` | `linarith only` |
| `AddComponentwiseLess` | componentwise `<` addition | `linarith only` |
| `AddComponentwiseLessLessEqual` | `<` plus `<=` | `linarith only` |
| `AddComponentwiseLessEqualLess` | `<=` plus `<` | `linarith only` |

Persistent tracer:
[`examples/05_compiler_interop/to_lean_builtin_rules_20.lit`](../../examples/05_compiler_interop/to_lean_builtin_rules_20.lit)

## Numeric object ABI

- [x] Freeze one uniform output spelling for every Litex `Obj`.
- [x] Keep symbols and normalized numerals bare; forbid per-object carrier
  inference and inserted numeric casts.
- [x] Keep `N`, `Z`, `Q`, `R`, and `C` as standard-set objects and parameter
  memberships rather than native Lean binder types.
- [x] Separate canonical object terms from optional native proof views.
- [x] Record natural, integer, rational, mixed-carrier, and rejected-boundary
  cases in a persistent Litex tracer.
- [ ] Select and implement the concrete `LitexObj` / `LitexSet` target model.
- [ ] Add structural `ObjToLeanIR` and monomorphic object-fact IR.
- [ ] Replace the real-only emitter without changing canonical object spelling.
- [ ] Promote the source tracer to an actual generated-Lean kernel gate.

Specification:
[`math_collections.md#numeric-object-abi`](math_collections.md#numeric-object-abi)

Tracer:
[`examples/05_compiler_interop/to_lean_numeric_obj_abi.lit`](../../examples/05_compiler_interop/to_lean_numeric_obj_abi.lit)

## Required final gates

- [x] Focused To-Lean release tests.
- [x] Direct release runner for every persistent tracer.
- [x] `cargo test --release run_examples -- --nocapture`.
- [x] `cargo test --release run_all -- --nocapture`.
- [x] Actual Lean kernel compilation for complete and incomplete outputs.
- [x] Targeted rustfmt check and workspace-hygiene audit.
