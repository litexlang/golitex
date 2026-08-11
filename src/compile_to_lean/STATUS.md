# Litex-to-Lean Implementation Status

Last updated: 2026-08-11

This file is the implementation ledger for the current Litex-to-Lean work. The
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
- [x] Preserve clause-coverage projections for unstored source `forall` facts,
  emit their real FactIds, and build checked conjunctions for stored
  multi-conclusion universals.

Tracer:
[`examples/05_compiler_interop/compile_to_lean_partial_report.lit`](../../examples/05_compiler_interop/compile_to_lean_partial_report.lit)

Projected-forall tracer:
[`examples/05_compiler_interop/compile_to_lean_mixed_projected_forall.lit`](../../examples/05_compiler_interop/compile_to_lean_mixed_projected_forall.lit)

## Native function and well-definedness ABI

- [x] Freeze `fn(...)` as `Set.univ` over a native dependent function type,
  while preserving `$in` as a proposition.
- [x] Freeze exact Litex application layers: value arguments first, then the
  same layer's ordered domain proofs; Lean currying does not widen source
  syntax.
- [x] Confirm with real Mathlib that a consumed local WD premise must have an
  explicit binder/helper name (an unnamed implication is not visible while
  its consequent type elaborates).
- [x] Retain statement-local WD proof certificates across temporary verifier
  scopes and boolean object-cache hits.
- [x] Lower bound function carriers and named applications, inserting only
  target-consumed certificate proofs as term arguments.
- [x] Replay source-only WD obligations as checked audit facts and reject
  missing, reordered, mismatched, or scope-invalid certificates.
- [x] Add the persistent function/WD tracer, malformed-evidence regressions,
  Markdown snapshot, and real Mathlib gate.
- [x] Add the first checked `have fn` declaration/evaluation slice for named,
  numeric-return function definitions, including exact defining-fact replay.
- [ ] Add standalone anonymous-function values, refined return-set evidence,
  and the remaining `have fn` forms as later slices of the same ABI.

Specification:
[`math_collections.md#native-function-sets-exact-layers-and-well-definedness-proofs`](math_collections.md#native-function-sets-exact-layers-and-well-definedness-proofs)

Tracer:
[`examples/05_compiler_interop/compile_to_lean_function_well_definedness.lit`](../../examples/05_compiler_interop/compile_to_lean_function_well_definedness.lit)

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
[`examples/05_compiler_interop/compile_to_lean_resolved_atomic_fact.lit`](../../examples/05_compiler_interop/compile_to_lean_resolved_atomic_fact.lit)

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
- [x] Lower `obtain ... from $P(args)` when the concrete definition has one
  positive `exist` clause by retaining the verified prop premise,
  re-instantiating and checking the definition projection, and emitting
  `simpa only [P]` before the ordinary existential-elimination path.
- [x] Reject verifier-certificate and backend-IR tampering for the named-prop
  projection, and compile its persistent ledger tracer with real Mathlib.
- [x] Lower `witness $P(args) from values` when the frozen concrete definition
  has exactly one plain positive `exist` clause. Retain the named prop as the
  primary fact, reuse checked existential introduction, fold it through a
  validated `DefinitionIntroduction`, and reject malformed IR.
- [x] Compile the persistent named-witness tracer with the real Mathlib kernel;
  keep `exist!`, `not exist`, abstract, nonexistential, and multi-clause targets
  as explicit v1 boundaries.
- [x] Check single- and multi-witness extraction with focused positive,
  malformed-evidence, sanitized-binder-capture, direct Litex, and real
  Mathlib/Lean gates.
- [ ] Add `exist!`/`not exist` proposition contracts and preimage selection.
- [x] Add checked declaration and evaluation evidence for the first named
  numeric-return `have fn ... = ...` form.
- [ ] Add anonymous, refined-return, case-by-case, recursive, tuple, sequence,
  and matrix `have` forms with their own evidence contracts.
- [ ] Add typed scope/exit contracts for induction, enumeration, extension,
  theorem/definition wrappers, and specialized relation/choice `by` commands.

Specification:
[`math_collections.md#statement-effects-and-proof-scopes`](math_collections.md#statement-effects-and-proof-scopes)

Tracer:
[`examples/05_compiler_interop/compile_to_lean_statement_scopes.lit`](../../examples/05_compiler_interop/compile_to_lean_statement_scopes.lit)

Choice tracer:
[`examples/05_compiler_interop/compile_to_lean_choice_have.lit`](../../examples/05_compiler_interop/compile_to_lean_choice_have.lit)

Existential tracer:
[`examples/05_compiler_interop/compile_to_lean_exist_have.lit`](../../examples/05_compiler_interop/compile_to_lean_exist_have.lit)

## Builtin rule inventory

- [x] Generate and audit the complete source-derived builtin rule inventory.
- [x] Record each rule's owning Rust file and checked Lean tactic/lemma mapping.
- [x] Mark evaluation/computation-like rules as `not_this_round`.

Current source audit: 466 direct success-constructor calls expand through
forwarding helpers to 659 label-bearing sites (632 rules and 27 strategies),
including 558 distinct static labels and 76 dynamic label expressions. There
are 46 evaluation/computation-like sites, of which 43 remain
`not_this_round` after the checked normalization and prime-reflection slices.
The checked mapping count is now 48 source sites. One of those sites is the
generic local-schema route and currently represents 86 paired RuleIds; source
site counts and paired-schema counts are deliberately reported separately.
The existing standard numeric-set nonemptiness route covers `N/Z/Q/R/C`.

Inventory:
[`builtin_rule_inventory.md`](builtin_rule_inventory.md)

## Structured builtin implementations

- [x] Add a paired local-builtin catalog: one restricted `.lit` forall schema
  and one checked `.lean` adapter per RuleId, with generated manifests and a
  whitespace-stable semantic fingerprint.
- [x] Use one generic `RegisteredLocal` verifier certificate and one generic
  `RegisteredRule` IR node instead of adding evidence/IR enum variants per
  ordinary fixed-pattern rule.
- [x] Revalidate RuleId, fingerprint, structural target bindings, parameter
  requirements, and ordered premise propositions before Lean emission; reject
  unknown IDs, stale fingerprints, and malformed arities.
- [x] Migrate 86 zero-, one-, and two-premise rules covering quotient/product
  nonzero, real absolute value/order, arithmetic signs and monotonicity,
  min/max, native union/intersection/set difference/powerset, set membership,
  finiteness,
  nonemptiness, and elementary subset laws, with a full real-Mathlib acceptance
  gate.

- [x] Quotient nonzero (`div_ne_zero`, including reversed orientation).
- [x] Not-equality symmetry (`Ne.symm` from one checked reversed premise).
- [x] Subset/superset duality with one retained reversed containment premise
  in all four positive/negative orientations.
- [x] Closed positive and negative `$prime` facts as native `Nat.Prime`
  propositions checked by `norm_num` reflection.
- [x] Standard numeric-set membership projection with one retained source
  membership proof, centralized hierarchy validation, and checked native
  coercions across the supported `N/Z/Q/R/C` paths.
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
[`examples/05_compiler_interop/compile_to_lean_builtin_rules_20.lit`](../../examples/05_compiler_interop/compile_to_lean_builtin_rules_20.lit)

Recursive-strategy tracer:
[`examples/05_compiler_interop/compile_to_lean_recursive_strategy_ir.lit`](../../examples/05_compiler_interop/compile_to_lean_recursive_strategy_ir.lit)

## Numeric object ABI

- [x] Keep structural `LitexToLeanObjectIr` identity separate from checked target
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
- [x] Instantiate dependent parameter carriers at each registered-rule
  occurrence (`x A` refers to the target `A`, not the catalog template symbol)
  without introducing a complete typed Fact IR.
- [ ] Give refined-domain prop parameters and unsupported scalar operators
  dedicated native contracts rather than relying on incidental elaboration.
- [ ] Extend the same occurrence-local carrier view only where new object
  families require it; a repository-wide typed Fact rewrite is not required.

Specification:
[`math_collections.md#numeric-object-abi`](math_collections.md#numeric-object-abi)

Tracer:
[`examples/05_compiler_interop/compile_to_lean_numeric_obj_abi.lit`](../../examples/05_compiler_interop/compile_to_lean_numeric_obj_abi.lit)

Structural set-object tracer:
[`examples/05_compiler_interop/compile_to_lean_set_obj_abi.lit`](../../examples/05_compiler_interop/compile_to_lean_set_obj_abi.lit)

Remaining native-carrier ledger:
[`todo/2026-8-10/to-lean-native-carrier.md`](../../todo/2026-8-10/to-lean-native-carrier.md)

## Required final gates

- [x] Focused Litex-to-Lean release tests.
- [x] Direct release runner for every persistent tracer.
- [x] `cargo test --release run_examples -- --nocapture`.
- [x] `cargo test --release run_all -- --nocapture`.
- [x] Actual Lean kernel compilation for complete and incomplete outputs.
- [x] Targeted rustfmt check and workspace-hygiene audit.
