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

## Statement effects and proof scopes

- [x] Lower explicit-value `have x T = e` as a checked object definition with
  its stored type and equality facts.
- [x] Distinguish file-scope `def` from proof-local `let` while keeping the same
  stable symbol identity.
- [x] Retain `by cases` branch-assumption `FactId`s before temporary
  environments are popped.
- [x] Lower binary complementary case coverage, local branch steps, conclusion
  exits, and contradiction exits to scoped Lean proofs.
- [x] Retain the `by contra` reverse-assumption `FactId` and lower atomic goals,
  local steps, and the final contradiction pair through
  `Classical.byContradiction`.
- [x] Retain the exact nonemptiness-result index and stored type fact for every
  bare `have x T` binding.
- [x] Lower `have x R` through `HaveObjChoice`, the existential
  `litexIsNonemptySet` ABI, `Exists.choose`, and `Exists.choose_spec` at both
  file and proof scope.
- [x] Reject missing or mismatched choice evidence, and keep meta-level
  parameter-type selection plus unsupported local statements as explicit
  incomplete boundaries with no `sorry` or compiler-created axiom.
- [x] Check the persistent statement-scope tracer with Litex, focused release
  tests, and the Lean core kernel.
- [x] Check the persistent typed-choice tracer with Litex, focused positive and
  malformed-evidence tests, and the Lean core kernel.
- [x] Retain concrete witness-type proofs outside temporary existential-binder
  scope, plus user proof steps and exact direct-body proof indices, for
  trust-free `witness exist` introduction.
- [x] Lower positive `obtain ... from exist` and body-style `have x T: ...`
  through checked alpha-equivalent source citations, ordered nested
  `Exists.choose`, and exact type/body `choose_spec` projections at file and
  proof scope.
- [x] Check single- and multi-witness extraction with focused positive,
  malformed-evidence, sanitized-binder-capture, direct Litex, and Lean-core
  gates.
- [ ] Add `exist!`/`not exist` proposition contracts and preimage selection.
- [ ] Add function-object declaration and evaluation evidence before compiling
  function, case-by-case, recursive, tuple, sequence, or matrix `have` forms.
- [ ] Add typed scope/exit contracts for induction, enumeration, extension,
  theorem/definition wrappers, and specialized relation/choice `by` commands.

Specification:
[`math_collections.md#statement-effects-and-proof-scopes`](math_collections.md#statement-effects-and-proof-scopes)

Tracer:
[`examples/05_compiler_interop/to_lean_statement_scopes.lit`](../../examples/05_compiler_interop/to_lean_statement_scopes.lit)

Choice tracer:
[`examples/05_compiler_interop/to_lean_choice_have.lit`](../../examples/05_compiler_interop/to_lean_choice_have.lit)

Existential tracer:
[`examples/05_compiler_interop/to_lean_exist_have.lit`](../../examples/05_compiler_interop/to_lean_exist_have.lit)

## Builtin rule inventory

- [x] Generate and audit the complete source-derived builtin rule inventory.
- [x] Record each rule's owning Rust file and checked Lean tactic/lemma mapping.
- [x] Mark evaluation/computation-like rules as `not_this_round`.

Current source audit: 462 direct success-constructor calls expand through
forwarding helpers to 658 label-bearing sites (631 rules and 27 strategies),
including 559 distinct static labels and 75 dynamic label expressions. There
are 46 evaluation/computation-like sites marked `not_this_round`.
The checked mapping count is now 26 sites: the prior normalization and
quotient-nonzero sites, the real-carrier nonemptiness shape used by checked
choice, the 20-rule tranche below, a second precise strict-to-weak call site,
and the typed recursive additive-strategy site.

Inventory:
[`builtin_rule_inventory.md`](builtin_rule_inventory.md)

## Structured builtin implementations

- [x] Quotient nonzero (`div_ne_zero`, including reversed orientation).
- [x] Select 20 representative non-evaluation builtin rules from the audited
  inventory.
- [x] Implement typed verifier evidence, compiler IR, checked Lean lowering,
  malformed-certificate regressions, and one persistent 20-rule tracer.
- [x] Preserve exact typed arithmetic evidence on additive builtin-strategy
  nodes while retaining the strategy label as diagnostic provenance.
- [x] Retain forall-scope inferred `R+` positivity facts with stable IDs and
  lower them through the checked `PositiveRealMembership` rule.
- [x] Reject mismatched recursive-strategy evidence and keep non-additive
  label-only strategies explicitly unsupported.
- [x] Check the recursive-strategy tracer through Litex, focused release tests,
  and a real Mathlib/Lean kernel.

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

Recursive-strategy tracer:
[`examples/05_compiler_interop/to_lean_recursive_strategy_ir.lit`](../../examples/05_compiler_interop/to_lean_recursive_strategy_ir.lit)

## Numeric object ABI

- [x] Freeze one uniform output spelling for every Litex `Obj`.
- [x] Keep symbols and normalized numerals bare; forbid per-object carrier
  inference and inserted numeric casts.
- [x] Keep `N`, `Z`, `Q`, `R`, and `C` as standard-set objects and parameter
  memberships rather than native Lean binder types.
- [x] Separate canonical object terms from optional native proof views.
- [x] Record natural, integer, rational, mixed-carrier, and rejected-boundary
  cases in a persistent Litex tracer.
- [x] Implement one concrete `LitexSet` target carrier; there is no separate
  semantic `LitexObj` type.
- [x] Add structural, context-free `ObjToLeanIR` with stable `SymbolId`s,
  normalized numerals, standard-set identity, and ordered applications.
- [x] Replace the real-only canonical emitter for the supported object tranche;
  native reals now occur only as checked proof-view payloads.
- [x] Lower `union`, `intersect`, `set_minus`, `set_diff`, big set operators,
  power sets, and list sets through the same object IR.
- [x] Reject binder-owning `SetBuilder` during IR construction instead of
  guessing a carrier or emitting a fallback.
- [x] Promote the structural set-object tracer to a generated-Lean core kernel
  gate.
- [ ] Replace the remaining raw `Fact` payload with a dedicated monomorphic
  structural object-fact IR.

Specification:
[`math_collections.md#numeric-object-abi`](math_collections.md#numeric-object-abi)

Tracer:
[`examples/05_compiler_interop/to_lean_numeric_obj_abi.lit`](../../examples/05_compiler_interop/to_lean_numeric_obj_abi.lit)

Structural set-object tracer:
[`examples/05_compiler_interop/to_lean_set_obj_abi.lit`](../../examples/05_compiler_interop/to_lean_set_obj_abi.lit)

## Required final gates

- [x] Focused To-Lean release tests.
- [x] Direct release runner for every persistent tracer.
- [x] `cargo test --release run_examples -- --nocapture`.
- [x] `cargo test --release run_all -- --nocapture`.
- [x] Actual Lean kernel compilation for complete and incomplete outputs.
- [x] Targeted rustfmt check and workspace-hygiene audit.
