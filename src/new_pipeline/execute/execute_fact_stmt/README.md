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

- `Ok(Equality(...))` / `Ok(AtomicExceptEquality(...))` when a proof route succeeds
- `Ok(Unknown(UnableToSearchProof))` when every search slot fails
- `Err(...)` only for real runtime / invariant failures

Search aggregators return `Ok(None)` on exhaustion; they must not emit
`Err(RuntimeError::Unknown)` for “no proof found”.

Must-prove callers (`execute_fact_statement`, WD requirements, `have`
nonempty obligations) reject `Unknown` at their boundary and must not `?`
treat it as proven evidence.

`verify_atomic_fact_search_proof` is the truth-proof phase after atomic-fact
well-definedness. Its ordinary search pipeline is intentionally limited to the
current `Runtime.execution_environments_stack` (including the parent scopes
represented by that stack). It does not search `Runtime.module_manager` or
merge loaded module main environments into ambient facts.

The stage also derives a read-only verification state, so trying proof routes
does not write new well-definedness records into the current scope.

The equality and atomic-except-equality pipelines keep their search slots in a fixed
order. Atomic-except-equality search is:

cache → builtin rule → known atomic → builtin strategy → by definition →
known forall → builtin algebraic rewrite → known algebraic rewrite.

`cache` is exact `FactIR` lookup in `KnownFactMemory.fact_ir_to_id` across the
current `execution_environments_stack`. The cache stores and cites **every**
closed `Fact` shape (atomic and composite). A cache hit requires full IR match
under name-is-identity; equality-class parameter matching and alpha-renaming
belong to later known-* slots, not cache. Do not index binder-internal open
scraps as ambient facts.

`CacheSearchProof` carries only `cite_fact_id` (payload lives in
`facts_by_id`). Design rationale and the identifier-conflict / do-not-break
checklist: [`../../identifier_identity.md`](../../identifier_identity.md).

Here `by definition` means ambient prop / builtin definition expansion in the
current execution-environment stack. Cross-module definitions and theorems are
still requested explicitly by `by def` or `by thm`, not by this search slot.
