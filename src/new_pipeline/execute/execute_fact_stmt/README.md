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

Atomic-fact WD (`verify_atomic_fact_well_definedness`) returns
`RuntimeResult<VerifyAtomicFactWellDefinedResult>`:

- `Ok(Success(AtomicFactWellDefinedProof))` when every argument Obj WD succeeds
- `Ok(Failed(FailToVerifyAtomicFactWellDefinedResult))` when some argument Obj WD
  soft-misses (`failed_arg_index` + `succeeded_args` + Obj `reason`)
- `Err(...)` only for real runtime / invariant failures

Fact WD dispatcher (`verify_fact_well_definedness`) returns
`RuntimeResult<VerifyFactWellDefinedResult>` with the same Success / Failed
split; fail payload is `FailToVerifyFactWellDefinedResult` (mirrors Fact:
index + nested WD fail, not a bare Obj fail). It only matches `Fact` and
delegates to `verify_xxx_fact_well_definedness`. Prefer the fine-grained
entry when the Fact shape is already known (and / chain / or / exist / atomic).

Object WD (`verify_obj_well_definedness`) returns
`RuntimeResult<VerifyObjWellDefinedResult>`:

- `Ok(ByKnown)` when a WD id is visible on the env stack
- `Ok(ByDef)` when WD is established by definition (and, if
  `store_well_defined_fact`, recorded on the current top env)
- `Ok(FailToVerifyWellDefined(reason))` when a child WD or requirement-fact
  search misses (`Child` / `Requirement` / `IdentifierUndefined` / `Others`)
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

The stage also derives a read-only verification state, so trying proof routes
does not write new well-definedness records into the current scope.

The equality and atomic-except-equality pipelines keep their search slots in a fixed
order. There is **no fact-level exact-IR cite** search slot (composites and
atomics alike). Object WD reuses recorded proofs via
`VerifyObjWellDefinedResult::ByKnown`.

Atomic-except-equality search is:

builtin rule → known atomic → builtin strategy → by definition →
known forall → builtin algebraic rewrite → known algebraic rewrite.

Equality search is:

builtin rule → known equality → builtin strategy → known forall.

`forall` local proof (when proving a forall fact) is:

introduce typed params → assume each dom (WD + store) → prove+store each then
→ take binder `local_env` (not merged). Parent stores the whole forall only on
Success, and projects then-clauses into
`KnownFactMemory.known_forall_conclusions` (`=` → `equal_conclusions`; other
atomics including `≠` → `by_atomic_prop`; whole `or` thens → `by_or`).

Atomic / equality / or search may then use `ByKnownForallFact` via
`SearchProofByKnownForallFact` (`cite: ForallConclusionCite` = FactId +
`ForallConclusionLocation`, plus instantiation args and requirement proofs).
And-then components are projected as `AndFactComponent` cites; exist thens
are not projected yet. Matching binds forall param identifiers
in then args; nested param occurrences inside compound objs are not matched yet.
Param-type obligations are not yet required at use (dom instantiation is).

`or` search order is:

WD of every branch → builtin (placeholder) → selected branch (always assume ¬ of
other atomic arms in a local env, then prove the selected arm) → known_or →
known_forall. Success payload carries `well_defined_proof` then `searched_proof`.

`KnownFactMemory` stores facts by `FactId` in `facts_by_id` and projects
searchable atomics into known-equality / known-atomic / known-forall indexes,
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
