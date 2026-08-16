# Litex-to-Lean implementation status

Last updated: 2026-08-14

This ledger describes only the universal-`Litex.Object` compiler. The former
native-carrier backend and its snapshots were deleted.

## Completed architecture checkpoint

- [x] One `Litex.Object` target type for values, sets, and functions.
- [x] The target ABI lives once in the shared `Litex.Core` Lake module;
  generated files import it through `Litex.Rules` and check ABI version
  9 instead of repeating the core.
- [x] `Litex.In x S` is independent membership evidence; it never retypes `x`.
- [x] `Litex.IsSet x` is the definitionally true pure-set proposition rather
  than a target type or classifier axiom, while set parameters retain their
  exact source proof and `FactId`.
- [x] `Litex.IsNonemptySet x` and `Litex.IsFiniteSet x` are derived definitions
  over the `In`-extension under the pure-set boundary, not independent axioms.
- [x] Standard numeric sets are `Litex.Object` constants.
- [x] Restricted `FnSpec`, separate `Applicable` evidence, and proof-free list
  application.
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
  parameter-requirement, and domain arguments. A direct atomic instance such
  as `$p(1)` is emitted as a theorem that applies the one trusted forall axiom;
  the atomic instance never becomes another axiom.
- [x] WD evidence retains runtime-owned `WellDefinedObjId` and
  `WellDefinedFactId` values and exact target requirement links.
- [x] The frozen WD graph has one identity system only. Direct object-to-fact
  edges use `WellDefinedFactId`; transitive facts are recovered through direct
  child edges. The former statement-local certificate IDs and duplicated
  transitive fact lists were removed so the two views cannot drift apart.
- [x] IR construction and Lean emission both validate the self-contained WD
  certificate: IDs are unique, roots and children exist, the object graph is
  acyclic and root-reachable, fact propositions are unchanged, target uses are
  owned by the cited object, and every frozen fact is attached to an object.
- [x] Object denotation is proof-free for arithmetic, division, list sets,
  application, and function objects. WD facts are replayed after `intro` as
  local `have wd_<environment-depth>_<id>` steps in the owning theorem or
  function-closure proof.
- [x] Every WD object node selected by the current theorem-local traversal
  closes over its direct children in child-before-parent order. Function
  applications additionally emit local `obj_N_applicable`; proper prefixes of
  layered calls are independent nodes, and local `obj_N_result` supplies their
  checked return membership to the next layer. Ordinary local object terms do
  not become top-level `obj_N` declarations. This does not yet claim that
  every frozen audit root is selected.
- [x] Root object uses retain their exact preflight/proof/store phase for
  audit. Every current certificate-bearing source family—function application,
  `+`/`-`/`*`/`/`, and list set—also has a parser-owned
  `SourceObjectOccurrenceId` and one frozen source-object-use edge. The emitter
  selects by that edge only; it no longer reconstructs an object ID from a
  semantic key or highest execution phase.
- [x] Structurally equal occurrences remain distinct while WD cache hits cite
  the same environment-owned `WellDefinedObjId`. When a parent cache hit skips
  recursive verification, its typed positional child recipe maps the new
  nested source occurrences directly to the already-checked child IDs.
- [x] Parent, temporary-child, and committed-child WD stores preserve the
  runtime's visibility and lifetime rules; proofless boolean cache entries are
  never compiler evidence.
- [x] Closed numeral membership is a Lean theorem derived from the numeric
  embedding core and stored in the shared builtin library.
- [x] Closed real-expression membership and positive-natural reflection have
  strict proof-rule adapters; neither route drops a retained environment fact
  or manufactures a generated axiom.
- [x] The first ordinary builtin adapter (`NotEqualSymmetry`) calls a real Lean
  theorem from the shared builtin library, with malformed shape rejected.
- [x] `Litex.add/sub/mul/div` are proof-free object constructors. Their source
  certificates still retain the verifier's two ordered `In operand C` facts;
  division additionally retains the exact denominator-nonzero fact. Complex
  and real closure are shared Lean theorems. Nested operations cite local
  `wd_<environment-depth>_<id>` steps, and each selected outer arithmetic
  object replays its frozen intrinsic `C` result as a local `obj_N_result`.
- [x] `Litex.listSet` is proof-free. Its source certificate retains the exact
  ordered element children and complete indexed `i < j` distinctness matrix,
  replayed locally. Two- and three-entry tracers compile under real Lean;
  missing, duplicated, misindexed, reversed, or retargeted slots fail closed
  before emission.
- [x] Universal arithmetic and rational normalization continue to cover the
  arithmetic nested-forall tracer under the proof-free denotation/local-WD
  ABI.
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
- [x] Every retained environment `FactId` in the supported successful
  statement IR emits or reuses exactly one Lean proof binding. Unsupported
  inferred facts fail compilation instead of disappearing silently.
- [x] Statement IR mirrors `Stmt` and its child enums recursively. Source
  statement names remain visible at the IR boundary; shared effect emission is
  implemented by functions rather than effect-shaped public variants.
- [x] Primary positive and missing-membership boundary tests.
- [x] Universal-object tracer, known-forall tracer, and ordinary builtin tracer
  compile as complete generated sources under real Mathlib.
- [x] One nonempty source argument group becomes one list application; nested
  groups use `Litex.fnSetResult`, and split arity remains rejected by Litex.
- [x] The executable feature ledger begins with the WD object DAG and trusted
  forall-to-atomic milestones; every entry compiles with the shared
  `Litex.Core`/`Litex.Rules` modules under real Mathlib. Earlier
  scenarios remain covered by the combined showcase and focused regressions.

## WD freeze boundary

The identity/lifetime kernel is ready to stabilize as an internal contract:

- `WellDefinedObjId` and `WellDefinedFactId` are monotone identities within
  one `Runtime`; their numeric values are intentionally not a serialized ABI
  and are not promised to repeat across compilations.
- Environment visibility owns cache visibility. A child sees its parent; only
  the referenced proof closure is promoted from a committed child; a closed or
  rolled-back child cannot leak evidence.
- A cache hit reuses the exact object node only under the exact selected
  function-membership `FactId`; a proofless ordinary cache entry is never
  compiler evidence. This observable invalidation rule is stable; the current
  rendered-`ObjString` cache-key representation is not a public ABI.
- Every frozen node stores direct child roles and direct fact edges only.
  Statement certificates are immutable, self-contained projections of the
  referenced environment closure.
- Every current certificate-bearing source occurrence freezes an exact
  occurrence-to-`WellDefinedObjId` edge plus its source-object snapshot.
  Missing, duplicated, or retargeted edges fail closed. This source-use
  contract is stable; the numeric occurrence values are not serialized ABI.

The complete WD construction ABI is **not frozen**. The old untyped-child
migration is complete: the 2026-08-14 source audit found 124 explicit
`verify_child_obj_well_defined_and_store_cache` call sites, 10 explicit
verification-dependency call sites, and zero direct recursive WD calls inside
the constructor verifier modules. `Unclassified` no longer exists. The value
edge layer is therefore substantially stronger than the previous audit said.

The remaining gaps are proof and resolution gaps rather than child-edge gaps:

- Function applications, `+`/`-`/`*`/`/`, list sets, ordered set-builder
  predicates, and the anonymous return closure expose exact construction-
  premise roles. Other partial
  constructors retain their successful facts in the audit DAG, but do not yet
  distinguish the semantic top-level WD conditions from proof-internal facts.
  Replacement still needs its uniqueness condition. Ranges and indexed or
  finite-set reductions now have typed value slots, proof-free denotations,
  and separate verification-dependency edges; their individual semantic
  conditions are not yet all classified into a target-neutral condition enum.
  Projections, indexing, matrices, structs, and similar constructors still
  need both that classification and typed resolution snapshots.
- A function-application cache key retains function-membership identities, but
  the frozen object node does not contain a self-contained snapshot of the
  exact selected layer specification. The validator can count argument
  membership slots, but only the later emitter currently rediscovers the exact
  domain-slot count from a separately registered function binding.
- Environment-dependent decisions such as the selected callable candidate,
  resolved struct field, template materialization, and normalized index are
  not yet a typed construction-resolution record. Intrinsic checks such as a
  nonempty rectangular matrix can be revalidated from the source snapshot;
  selected environment results cannot be reconstructed after scope exit.
- Anonymous functions own one exact binder scope. Compound bodies such as
  `fn(x R) R {x + 1}` now keep the body `Object` term proof-free and replay
  their WD/return closure in the generated owner `closed` theorem after the
  parameter and domain telescope is introduced. The generalized helper
  declarations are still hoisted; consolidating those declarations into a
  smaller source-theorem-local presentation is an output-shape improvement,
  not a missing proof-scope contract.
- Set builders now freeze their parameter membership and every predicate as
  source-ordered binder premises. `have S set = {x R: x != 0, 1 / x > 0}`
  emits a definition-theorem-local dependent `Prop` audit whose quotient WD
  proof cites the preceding nonzero FactId. The `Litex.setBuilder` term itself
  remains proof-free. Function sets still need the same fully target-neutral
  recipe for dependent return-carrier construction.
- Active-object recursion suppression remains an ordinary Litex runtime
  optimization, but To-Lean capture now fails closed if the same active object
  is re-entered before its `WellDefinedObjId` is complete. A future accepted
  recursive revisit must first gain an explicit typed binder/source-only edge;
  it can no longer silently create a missing construction edge.
- Set-builder parameter carriers and finite-set extrema no longer add a second
  verifier-only edge for the same object immediately after recording their
  real construction child. This removes audit noise without removing a Litex
  check or proof condition.
- The emitter remains demand-driven and only certificate-bearing source families
  have parser-owned occurrence IDs. Emitting every auditable WD root requires
  a general occurrence/selection contract and renderable construction recipes.

Do not freeze the current small `WellDefinednessRequirementRole` enum, the
cache key's deduplicated function-contract vector, the demand-only emitter
selection, or rendered object strings as WD cache identity. Those are internal
migration scaffolding, not the final object-construction ABI.

## Required next coverage

- [x] Implement the decided all-objects-are-sets ABI: `IsSet` is
  definitionally `True`, and nonempty/finite predicates contain only their
  membership content.
- [x] Add proof-free list-set denotation with an ordered child and
  pairwise-distinct source certificate replayed locally.
- [x] Lower big union/intersection, power set, general Cartesian products,
  half-open/closed integer ranges, indexed and finite-set sum/product/reduce,
  tuple/sequence literals, and finite/infinite sequence carriers to proof-free
  `Litex.Object` terms. Closed-range aggregate rechecks are frozen as audit
  dependencies rather than constructor value slots.
- [ ] Replace the target-named proof-slot layer with a verifier-owned,
  target-neutral construction recipe: ordered value children, indexed semantic
  condition proofs, owned binder scopes, and typed environment-resolution
  decisions. Every top-level WD condition must be classified separately from
  proof-internal audit facts.
- [ ] Freeze the exact selected function-layer specification in each
  application recipe; the frozen WD validator must verify argument, domain,
  and result slots without consulting emitter-side function bindings.
- [x] Reject an active-object recursive re-entry during To-Lean capture unless
  it already resolves to a completed reusable `WellDefinedObjId`; ordinary
  Litex verification retains its historical suppression behavior.
- [x] Upgrade `FnSpec`/`functionObject` to a proof-aware ABI: ordered
  requirements are a dependent existential telescope in `Prop`, and both the
  body and range may use exact arity/requirements evidence. `functionObject`
  itself no longer consumes its closure proof. Named functions replay
  arithmetic and partial-body WD locally through their frozen
  `WellDefinedObjId`/`WellDefinedFactId` DAGs.
- [x] Connect compound anonymous bodies to owner-closure replay. Parameter and
  domain premises are introduced before the compound WD DAG and return proof;
  the `functionObject` body remains a proof-free term.
- [ ] Add the remaining partial object constructors, beginning with
  replacement. Their Lean terms must remain proof-free while the
  verifier-owned WD construction recipe is replayed in the corresponding Lean
  proof environment rather than as detached top-level declarations.
- [x] Preserve and emit the supported positive-real inferred forall premise.
- [ ] Add dependent/refined non-function return-set coverage beyond the current
  nested function-set result path.
- [ ] Add the remaining unified object operations and closure theorems,
  including power, transcendental functions, and refined numeric sets.
- [ ] Port builtin families over `Litex.Object`: standard-set hierarchy,
  arithmetic/order, refined membership, set operators, reflection, and
  registered rules. Each checked certificate must call one theorem schema in
  `Litex.Rules`; no per-use tactic expansion or builtin axiom fallback.
- [ ] Lower the remaining definition and statement boundaries. Object choice,
  positive one-witness existentials, cases/contradiction, named theorems, set
  builders, named functions, and compound anonymous functions have
  focused recipes; bodyless concrete props, `trust have`, wider
  existential/case forms, namespaces, and proof-dependent binder recipes
  remain explicit gaps.
- [ ] Restore transactional incomplete-report mode on the new emitter.
- [ ] Append every newly supported capability to the executable feature ledger
  with its harness source, generated shape, rejected boundary, focused tests,
  and real-Mathlib gate.

No unchecked item may be satisfied by reintroducing native carriers or by
falling back to the deleted emitter.
