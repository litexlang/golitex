# To-Lean Implementation Status

Last updated: 2026-08-10

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
- [x] Small self-contained compiler examples use one paired-fence Markdown
  ledger whose Litex inputs and generated Lean snapshots are checked together.

Tracer:
[`examples/05_compiler_interop/to_lean_partial_report.lit`](../../examples/05_compiler_interop/to_lean_partial_report.lit)

## Resolved atomic facts

- [x] Retain goal-to-source resolution as an ordered source-to-goal
  transformation package.
- [x] Separate recursive rational normalization from equality rewrite and keep
  every used equality's stored `FactId`.
- [x] Replay the supported arithmetic route as nested proof IR and checked Lean
  without rerunning `resolve_obj`.
- [x] Descend through nested object shapes, including function arguments, while
  keeping unsupported general function objects as an explicit Obj IR boundary.
- [x] Replay a stored equality between compound subobjects at any depth covered
  by the central structural matcher, without flattening it into resolution.
- [x] Add a persistent arithmetic tracer plus focused supported and boundary
  regressions.

Specification:
[`math_collections.md#resolved-atomic-fact-transformations`](math_collections.md#resolved-atomic-fact-transformations)

Tracer:
[`examples/05_compiler_interop/to_lean_resolved_atomic_fact.lit`](../../examples/05_compiler_interop/to_lean_resolved_atomic_fact.lit)

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
  tests, and the real Mathlib/Lean kernel.
- [x] Check the persistent typed-choice tracer with Litex, focused positive and
  malformed-evidence tests, and the real Mathlib/Lean kernel.
- [x] Retain concrete witness-type proofs outside temporary existential-binder
  scope, plus user proof steps and exact direct-body proof indices, for
  trust-free `witness exist` introduction.
- [x] Lower positive `obtain ... from exist` and body-style `have x T: ...`
  through checked alpha-equivalent source citations, ordered nested
  `Exists.choose`, and exact type/body `choose_spec` projections at file and
  proof scope.
- [x] Check single- and multi-witness extraction with focused positive,
  malformed-evidence, sanitized-binder-capture, direct Litex, and real
  Mathlib/Lean gates.
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
forwarding helpers to 657 label-bearing sites (630 rules and 27 strategies),
including 558 distinct static labels and 74 dynamic label expressions. There
are 46 evaluation/computation-like sites, of which 43 remain
`not_this_round` after the checked normalization and prime-reflection slices.
The checked mapping count is now 46 sites: the previous 32, six native set
equalities, four native set-membership routes, and four absolute-value routes.
The existing standard numeric-set nonemptiness route now covers `N/Z/Q/R/C`.

Inventory:
[`builtin_rule_inventory.md`](builtin_rule_inventory.md)

## Structured builtin implementations

- [x] Quotient nonzero (`div_ne_zero`, including reversed orientation).
- [x] Not-equality symmetry (`Ne.symm` from one checked reversed premise).
- [x] Subset/superset duality with one retained reversed containment premise
  in all four positive/negative orientations.
- [x] Closed positive and negative `$prime` facts as native `Nat.Prime`
  propositions checked by `norm_num` reflection.
- [x] Native proposition lowering for superset, proper subset/superset, and all
  four negated comparisons.
- [x] Native `Set` equality lowering for union/intersection commutativity and
  associativity, union idempotence, and union-empty identity.
- [x] Native `Set` membership introduction for union, intersection, and
  set-minus, including checked premise-arity rejection.
- [x] Native absolute-value identities for nonnegative/nonpositive inputs and
  multiplicative products, plus strict positivity from a nonzero premise.
- [x] Expand the standard nonempty-set witness route from `R` to `N`, `Z`,
  `Q`, `R`, and `C` while retaining native Mathlib carriers.
- [x] Select 20 representative non-evaluation builtin rules from the audited
  inventory.
- [x] Implement typed verifier evidence, compiler IR, checked Lean lowering,
  malformed-certificate regressions, and one persistent 20-rule tracer.
- [x] Preserve exact typed arithmetic evidence on additive builtin-strategy
  nodes while retaining the strategy label as diagnostic provenance.
- [x] Retain forall-scope inferred `R+` positivity facts with stable IDs and
  lower them through the checked `PositiveRealMembership` rule.
- [x] Lower closed membership and nonmembership facts over `N+`/`Z+`, `Q+`,
  `R+`, `Z-`, `Q-`, `R-`, `Z*`, `Q*`, `R*`, and `C*` through carrier-bearing
  checked numeric reflection (`norm_num`), without assigning an intrinsic
  carrier to bare numerals.
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

- [x] Keep structural `ObjToLeanIR` identity separate from checked target
  carrier constraints.
- [x] Map `N`, `Z`, `Q`, `R`, and `C` to `Set.univ` over Mathlib's
  `ℕ`, `ℤ`, `ℚ`, `ℝ`, and `ℂ`.
- [x] Emit standard-domain parameters as bounded quantifiers so membership
  remains an ordinary named proposition.
- [x] Keep numerals and symbols bare in structural object output.
- [x] Insert a whole-expression target expectation only for a justified
  canonical numeric coercion; the retained `ℤ -> ℚ` tracer passes the real
  Mathlib/Lean kernel.
- [x] Replace private equality/arithmetic wrappers with native `=`, `+`, `-`,
  `*`, and `/` in the migrated object/fact surface.
- [x] Replace the monomorphic target prelude with a polymorphic `LitexObject`
  marker that does not admit facts as source objects.
- [x] Lower generic set binders through an implicit element carrier and native
  `Set α`; map `union`, `intersect`, and `set_minus` to `∪`, `∩`, and `\`.
- [x] Reject binder-owning `SetBuilder` during IR construction instead of
  guessing a carrier or emitting a fallback.
- [x] Propagate checked carrier constraints through known-forall,
  normalization, equality-rewrite, existential, and forall-introduction proof
  trees; the resolved-atomic regression prevents an intermediate `ℕ` default
  from crossing an `ℝ` goal.
- [ ] Give refined-domain prop parameters and unsupported scalar operators
  dedicated native contracts rather than relying on incidental elaboration.
- [ ] Replace the remaining raw `Fact` payload with a dedicated typed
  structural object-fact IR.

Specification:
[`math_collections.md#numeric-object-abi`](math_collections.md#numeric-object-abi)

Tracer:
[`examples/05_compiler_interop/to_lean_numeric_obj_abi.lit`](../../examples/05_compiler_interop/to_lean_numeric_obj_abi.lit)

Structural set-object tracer:
[`examples/05_compiler_interop/to_lean_set_obj_abi.lit`](../../examples/05_compiler_interop/to_lean_set_obj_abi.lit)

Remaining native-carrier ledger:
[`todo/2026-8-10/to-lean-native-carrier.md`](../../todo/2026-8-10/to-lean-native-carrier.md)

## Required final gates

- [x] Focused To-Lean release tests.
- [x] Direct release runner for every persistent tracer.
- [x] `cargo test --release run_examples -- --nocapture`.
- [x] `cargo test --release run_all -- --nocapture`.
- [x] Actual Lean kernel compilation for complete and incomplete outputs.
- [x] Targeted rustfmt check and workspace-hygiene audit.
