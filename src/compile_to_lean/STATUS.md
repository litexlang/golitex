# Litex-to-Lean implementation status

Last updated: 2026-08-13

This ledger describes only the universal-`LitexObject` compiler. The former
native-carrier backend and its snapshots were deleted.

## Completed architecture checkpoint

- [x] One `LitexObject` target type for values, sets, and functions.
- [x] `Litex.In x S` is independent membership evidence; it never retypes `x`.
- [x] `Litex.IsSet x` is represented as a proposition rather than a target
  type, and set parameters retain their exact source proof.
- [x] `Litex.IsNonemptySet x` and `Litex.IsFiniteSet x` are derived definitions
  over `IsSet` and the `In`-extension, not independent axioms.
- [x] Standard numeric sets are `LitexObject` constants.
- [x] Restricted `FnSpec`, proof-carrying `Applicable`, and list application.
- [x] Exact source application layers retained by object IR.
- [x] Native carrier IR, type unification, widening/downcast logic, and native
  set/function prelude removed.
- [x] Public compiler entry points select only the new emitter.
- [x] Forall introduction binds every object as `LitexObject` and retains every
  parameter membership or set-property fact.
- [x] Known facts resolve by exact `FactId`.
- [x] Known equality classes expose their existing direct proof paths; every
  selected edge is joined to its exact cached `FactId`, symmetry and multi-edge
  transitivity emit `Eq.symm`/`Eq.trans`, and discarded child environments do
  not leak evidence.
- [x] Known forall instances call the exact source `FactId` with ordered object,
  parameter-requirement, and domain arguments.
- [x] WD evidence retains runtime-owned `WellDefinedObjProofId` and
  `WellDefinedFactId` values and exact target requirement links.
- [x] WD facts needed in theorem types are emitted first as generalized helper
  theorems and cited by stable ID.
- [x] Every parsed function application has a `SourceObjectOccurrenceId`.
  Structurally equal occurrences remain distinct, while WD cache hits cite the
  same environment-owned `WellDefinedObjProofId` and `WellDefinedFactId`.
- [x] Parent, temporary-child, and committed-child WD stores preserve the
  runtime's visibility and lifetime rules; proofless boolean cache entries are
  never compiler evidence.
- [x] Closed numeral membership is a Lean theorem derived from the numeric
  embedding core.
- [x] The first ordinary builtin adapter (`NotEqualSymmetry`) calls a real Lean
  theorem, with malformed shape rejected.
- [x] Universal `Litex.add/sub/mul/div` operations, real-closure certificates,
  and rational normalization cover the arithmetic nested-forall tracer.
- [x] Nested forall premises retain their temporary parameter `FactId`s and
  replay them as exact Lean binder proofs.
- [x] Primary positive and missing-membership boundary tests.
- [x] Universal-object tracer, known-forall tracer, and ordinary builtin tracer
  compile as complete generated sources under real Mathlib.
- [x] One nonempty source argument group becomes one list application; nested
  groups use `Litex.fnSetResult`, and split arity remains rejected by Litex.
- [x] The eight-entry universal-object ledger compiles under real Mathlib.

## Required next coverage

- [ ] Implement the decided all-objects-are-sets ABI: replace the currently
  emitted opaque `Litex.IsSet` with `def IsSet (_ : LitexObject) := True`, and
  simplify the derived nonempty/finite predicates. The exact current drift is
  preserved in `current_generated_file_header.lean`.
- [ ] Add proof-carrying partial object constructors, beginning with list sets,
  replacement, and anonymous functions. Their Lean terms must consume the
  verifier-owned WD certificates instead of retaining those facts only as
  detached audit declarations.
- [ ] Preserve and emit supported inferred forall premises.
- [ ] Add dependent/refined non-function return-set coverage beyond the current
  nested function-set result path.
- [ ] Add the remaining unified object operations and closure theorems,
  including power, transcendental functions, and refined numeric sets.
- [ ] Port builtin families over `LitexObject`: standard-set hierarchy,
  arithmetic/order, refined membership, set operators, reflection, and
  registered rules.
- [ ] Lower user proposition definitions, set builders, anonymous functions,
  named function definitions, object definitions/choice, existentials,
  cases/contradiction, named theorems, and namespaces.
- [ ] Restore transactional incomplete-report mode on the new emitter.
- [ ] Rebuild the consolidated exact-output ledger and repository-wide real
  Mathlib gate as coverage grows.

No unchecked item may be satisfied by reintroducing native carriers or by
falling back to the deleted emitter.
