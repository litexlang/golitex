# Litex-to-Lean implementation status

Last updated: 2026-08-13

This ledger describes only the universal-`Litex.Object` compiler. The former
native-carrier backend and its snapshots were deleted.

## Completed architecture checkpoint

- [x] One `Litex.Object` target type for values, sets, and functions.
- [x] The target ABI lives once in the shared `Litex.Core` Lake module;
  generated files import it through `Litex.BuiltinRules` and check ABI version
  2 instead of repeating the core.
- [x] `Litex.In x S` is independent membership evidence; it never retypes `x`.
- [x] `Litex.IsSet x` is represented as a proposition rather than a target
  type, and set parameters retain their exact source proof.
- [x] `Litex.IsNonemptySet x` and `Litex.IsFiniteSet x` are derived definitions
  over `IsSet` and the `In`-extension, not independent axioms.
- [x] Standard numeric sets are `Litex.Object` constants.
- [x] Restricted `FnSpec`, proof-carrying `Applicable`, and list application.
- [x] Exact source application layers retained by object IR.
- [x] Native carrier IR, type unification, widening/downcast logic, and native
  set/function prelude removed.
- [x] Public compiler entry points select only the new emitter.
- [x] Forall introduction binds every object as `Litex.Object` and retains every
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
- [x] Root object uses retain their exact preflight/proof/store phase. Equal
  source arithmetic nodes select the proof-phase root and then follow exact
  child edges; the emitter never chooses among WD nodes by proposition text.
- [x] Every parsed function application has a `SourceObjectOccurrenceId`.
  Structurally equal occurrences remain distinct, while WD cache hits cite the
  same environment-owned `WellDefinedObjProofId` and `WellDefinedFactId`.
- [x] Parent, temporary-child, and committed-child WD stores preserve the
  runtime's visibility and lifetime rules; proofless boolean cache entries are
  never compiler evidence.
- [x] Closed numeral membership is a Lean theorem derived from the numeric
  embedding core and stored in the shared builtin library.
- [x] The first ordinary builtin adapter (`NotEqualSymmetry`) calls a real Lean
  theorem from the shared builtin library, with malformed shape rejected.
- [x] `Litex.add/sub/mul` are proof-carrying constructors: each term consumes
  the verifier's two ordered `In operand C` facts. Complex and real closure are
  shared Lean theorems, and nested operations cite earlier
  `well_defined_fact_<id>` helpers. `Litex.div` remains the explicit boundary.
- [x] Universal arithmetic and rational normalization continue to cover the
  arithmetic nested-forall tracer under the proof-carrying ABI.
- [x] Nested forall premises retain their temporary parameter `FactId`s and
  replay them as exact Lean binder proofs.
- [x] `abstract_prop` emits one uninterpreted predicate declaration; bodyful
  `prop` emits one universal-object `def` whose conjunction includes ordered
  parameter requirements and definition clauses.
- [x] Explicit-value object `have name S = value` emits one
  `noncomputable def`, then checked membership and defining-equality theorems
  under their retained `FactId`s.
- [x] Concrete `by def` retains exact parameter and clause child proofs.
  Definition consequences are projected from that theorem rather than
  re-proved by target search.
- [x] Only an explicit `trust fact` becomes an axiom. Inferred consequences
  and later citations emit or reuse theorems; duplicate `FactId`s are reused
  only when their propositions agree exactly.
- [x] Primary positive and missing-membership boundary tests.
- [x] Universal-object tracer, known-forall tracer, and ordinary builtin tracer
  compile as complete generated sources under real Mathlib.
- [x] One nonempty source argument group becomes one list application; nested
  groups use `Litex.fnSetResult`, and split arity remains rejected by Litex.
- [x] The ten-entry universal-object ledger compiles with the shared
  `Litex.Core`/`Litex.BuiltinRules` modules under real Mathlib.

## Required next coverage

- [ ] Implement the decided all-objects-are-sets ABI: replace the currently
  shared opaque `Litex.IsSet` with `def IsSet (_ : Litex.Object) := True`, and
  simplify the derived nonempty/finite predicates. The exact current drift is
  preserved in `lean/Litex/Core.lean`.
- [ ] Add proof-carrying partial object constructors, beginning with list sets,
  replacement, and anonymous functions. Their Lean terms must consume the
  verifier-owned WD certificates instead of retaining those facts only as
  detached audit declarations.
- [ ] Migrate `Litex.div` after freezing its three ordered target obligations:
  numerator in `C`, denominator in `C`, and denominator nonzero.
- [ ] Preserve and emit supported inferred forall premises.
- [ ] Add dependent/refined non-function return-set coverage beyond the current
  nested function-set result path.
- [ ] Add the remaining unified object operations and closure theorems,
  including power, transcendental functions, and refined numeric sets.
- [ ] Port builtin families over `Litex.Object`: standard-set hierarchy,
  arithmetic/order, refined membership, set operators, reflection, and
  registered rules. Each checked certificate must call one theorem schema in
  `Litex.BuiltinRules`; no per-use tactic expansion or builtin axiom fallback.
- [ ] Lower the remaining definition and statement families: bodyless
  concrete-proposition semantics, set builders, anonymous and named function
  definitions, object choice, `trust have`, existentials,
  cases/contradiction, named theorems, and namespaces.
- [ ] Restore transactional incomplete-report mode on the new emitter.
- [ ] Rebuild the consolidated exact-output ledger and repository-wide real
  Mathlib gate as coverage grows.

No unchecked item may be satisfied by reintroducing native carriers or by
falling back to the deleted emitter.
