# Staged verifier draft

`src/verify` is the in-tree draft of the verifier rewrite. It uses the
canonical fact, environment, runtime, and identifier types from the rest of
the crate, but it is exposed under `litex::verify_rewrite` so it does not take
ownership of the running verifier yet.

The compatibility path remains `litex::verify`, backed by
`litex::verification`. Result and pipeline files in this directory can be
developed in parallel; they are added to the draft module as their runtime
ownership is migrated, rather than compiling a second set of `Runtime`
methods at the same time.

The foundational correspondence is intentional:

```text
The new pipeline owns its runtime IDs in `runtime::runtime_ids`.
`runtime::runtime_ids::FactId` is intentionally independent from the legacy
`fact::id::FactId`; compatibility, if needed later, must be explicit.
Verifier result types mostly mirror Fact shape; atomic facts flatten to
Equality / AtomicExceptEquality on VerifyFactResult (no AtomicFact wrapper).
```

This keeps FactIds and temporary environments compatible with later Lean
consumers while the new Result and pipeline shapes are still being drafted.

## Atomic-fact search boundary

`verify_atomic_fact` (after well-definedness) returns
`RuntimeResult<VerifyFactResult>`:

- `Ok(Equality(Success(...)))` / `Ok(AtomicExceptEquality(Success(...)))` when a proof route succeeds
- `Ok(Equality(Failed(FailToVerifyWellDefined(...))))` (or AtomicExcept…) when object WD is not established
- `Ok(Equality(Failed(FailToSearchProof { ... })))` when WD succeeds but every truth-search slot fails
- `Err(...)` only for real runtime / invariant failures

Each fact-kind `VerifyXXXResult` is `Success(...) | Failed(WD | SearchProof)`.
`VerifyFactResult` only mirrors `Fact` (no top-level Fail variants).
And/Chain/Forall soft misses stay under `AndFact(Failed(...))` /
`ChainFact(Failed(...))` / `ForallFact(Failed(...))`.

### Proof vs Result

`*Proof` is success evidence only. Soft miss belongs on a `*Result`
(`Success(Proof) | Failed(...)`, or an enum with explicit Fail variants).
Do not embed Fail inside a Proof and call `is_failed()` on that Proof.

Atomic-fact WD (`verify_atomic_fact_well_definedness`) is for
atomic-except-equality only and returns
`RuntimeResult<VerifyAtomicFactWellDefinedResult>`:

- `Ok(Success(AtomicFactWellDefinedProof))` when every argument Obj WD succeeds
  (`well_defined_of_each_parameter: Vec<ObjWellDefinedProof>`)
- `Ok(Failed(FailToVerifyAtomicFactWellDefinedResult { reason }))` when some
  argument Obj WD soft-misses (`reason` is the Obj fail only)
- `Err(...)` only for real runtime / invariant failures (including calling it on
  `EqualFact`)

Equality WD (`verify_equal_fact_well_definedness`) is independent and returns
`RuntimeResult<VerifyEqualFactWellDefinedResult>`:

- `Ok(Success(EqualFactWellDefinedProof { left, right }))` when both sides succeed
  (`left` / `right` are `ObjWellDefinedProof`)
- `Ok(Failed(FailToVerifyEqualFactWellDefinedResult { reason }))` when left or
  right soft-misses (`reason` is the Obj fail only)
- `Err(...)` only for real runtime / invariant failures

Fact WD dispatcher (`verify_fact_well_definedness`) returns
`RuntimeResult<VerifyFactWellDefinedResult>` with the same Success / Failed
split; fail payload is `FailToVerifyFactWellDefinedResult` (mirrors Fact:
index + nested WD fail, not a bare Obj fail). Success proof splits
`Equality` vs `AtomicExceptEquality`. It only matches `Fact` and
delegates to `verify_xxx_fact_well_definedness`. Prefer the fine-grained
entry when the Fact shape is already known (and / chain / or / exist /
equal / atomic-except-equality).

Object WD (`verify_obj_well_definedness`) returns
`RuntimeResult<VerifyObjWellDefinedResult>`:

- `Ok(Success(ByKnown { wd_id }))` when a WD id is visible on the env stack
- `Ok(Success(ByDef(proof)))` when by-definition succeeds; `ObjWellDefinedProofByDef`
  mirrors `Obj` (one dedicated proof struct per variant). Scalar (P0),
  identifier-headed `FnObj`, binder objects (`FnSet` / `AnonymousFn` /
  `SetBuilder` with `local_env`), and cart/index (`CartDim` / `Proj` /
  `TupleDim` / `ObjAtIndex`) fill named semantic requirements; many other
  set/iterated constructors remain children-only until later slices
- `Ok(Failed(reason))` when a child WD or requirement soft-misses;
  `FailToVerifyObjWellDefinedResult` also mirrors `Obj`
- `Err(...)` only for real runtime / invariant failures

Requirement search aggregators return soft fail variants on exhaustion; they
must not emit `Err(RuntimeError::Unknown)` for “no proof found”.

Nested must-prove callers reject soft fails at their boundary. Top-level soft
fails become a leaf `*Result::Failed` inside `ExecStmtResult` (temp env
discarded, no merge).

`exec_stmt` always runs the stmt in a temp `ExecEnv` and merges only when
`!outcome.is_failed()`.

`verify_atomic_fact_search_proof` is the truth-proof phase after atomic-fact
well-definedness. Its ordinary search pipeline is intentionally limited to the
current `Runtime.execution_environments_stack` (including the parent scopes
represented by that stack). It does not search `Runtime.global_module_manager` or
merge loaded module main environments into ambient facts.

Qualified **definition** lookup is separate: `def_prop_visible` /
`def_thm_visible` (and `release obj def`) may resolve a `mod::export::`-qualified
name in a finished export file's recorded `ExecEnv`. That brings a named
definition into the current statement; it does not dump that export's known-fact
table into ambient search.

The stage also derives a read-only verification state, so trying proof routes
does not write new well-definedness records into the current scope.

The equality and atomic-except-equality pipelines keep their search slots in a fixed
order. There is **no fact-level exact-IR cite** search slot (composites and
atomics alike). Object WD reuses recorded proofs via
`VerifyObjWellDefinedResult::Success(ObjWellDefinedProof::ByKnown { .. })`.

Atomic-except-equality search is:

builtin rule → known atomic → builtin strategy → by definition →
known forall → builtin algebraic rewrite → known algebraic rewrite.

Equality search is:

builtin rule → equivalence class → builtin strategy → MatchingOneArgByOne →
known forall → builtin rewrite (ClosedNumericEqualSubstitution, KnownEqualObjSubstitution, OrderDual).

MatchingOneArgByOne peels same-shape constructors (numeric, FnObj application
layers, sets/tuples/carts, ranges, sums/products/reduces, struct field access,
…); binder shapes (SetBuilder / AnonymousFn / FnSet) are intentionally skipped.

`forall` local proof (when proving a forall fact) is:

introduce typed params → assume each dom (WD + store) → prove+store each then
→ take binder `local_env` (not merged). Parent stores the whole forall only on
Success, and projects then-clauses into
`KnownFactMemory.known_forall_conclusions` (`=` → `equal_conclusions`; other
atomics including `≠` → `by_atomic_prop`; whole `or` thens → `by_or`).

Atomic / equality / or / exist search may then use `ByKnownForallFact` via
`SearchProofByKnownForallFact` (`cite: ForallConclusionCite` = FactId +
location into then / and-component / exist-then). Equality also tries the
swapped sides and records `ByKnownForallFactViaSymmetry` when the forall
matches only after reversing `L = R` (legacy equality symmetry).
`ForallConclusionLocation`, ordered `forall_parameters_match_what_args`,
per-arg `arg_match_proofs` (`BoundParam` / `ReboundParamEqual` /
`NonParamEqual` with `StrictEqualWithFact`), then
`instantiation_requirements` from `prove_forall_instantiation_requirements`:
param-type facts (same shapes as introduce: `$in` / `isSet` / …) verified per
parameter, then instantiated dom facts verified).
And-then components are projected as `AndFactComponent` cites; exist thens
are projected into `by_exist`. Matching is shared
(`match_forall_conclusion_args`): bind bare forall params; recurse into
same-shape compounds (`FnObj`, arithmetic, `FieldAccess`, …) via
`ByStructure` child proofs (legacy-aligned); otherwise instantiate the
pattern under the subst so far and prove `pattern_after_subst = goal` by
equal search with all `VerifyState` flags false (`can_use_forall_fact`,
`can_use_rewrite`, `store_well_defined_fact`; certificate type
`StrictEqualArgProof`). Nested param occurrences inside compound objs are
bound during that structural recursion. Exist apply also instantiates the
conclusion and alpha-compares to the goal before instantiation requirements.

`or` search order is:

WD of every branch → builtin (placeholder) → selected branch (always assume ¬ of
other atomic arms in a local env, then prove the selected arm) → known_or →
known_forall. Success payload carries `well_defined_proof` then `searched_proof`.

`KnownFactMemory` stores facts by `FactId` in `facts_by_id` and projects
searchable atomics into known_equivalence_classes / known-atomic / known-forall indexes,
and whole ors into `known_or` (structural key; branches are not split).
And/chain store also records the whole fact, then stores adjacent (and for
comparison chains, transitive closures with BuiltinEquality /
BuiltinNumericOrder / KnownTransitive cites). There is no whole-fact exact-IR
cite path for verify. Design rationale and the identifier-conflict /
do-not-break checklist:
[`../../identifier_identity.md`](../../identifier_identity.md).

Here `by definition` means ambient prop / builtin definition expansion in the
current execution-environment stack. Cross-module definitions and theorems are
still requested explicitly by `by def` or `by thm`, not by this search slot.
