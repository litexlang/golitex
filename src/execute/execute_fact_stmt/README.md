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
Runtime IDs live in `runtime::runtime_ids`.
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

- `Ok(Success(ByKnown { obj, wd_id }))` when a WD id is visible on the env stack
- `Ok(Success(ByDef { obj, proof }))` when by-definition succeeds;
  `ObjWellDefinedProofByDef` mirrors `Obj` (one dedicated proof struct per
  variant). Scalar (P0), identifier-headed `FnObj`, binder objects (`FnSet` /
  `AnonymousFn` / `SetBuilder` with `local_env`), and cart/index (`CartDim` /
  `Proj` / `TupleDim` / `ObjAtIndex`) fill named semantic requirements; many
  other set/iterated constructors remain children-only until later slices
- `Ok(Failed { obj, reason })` when a child WD or requirement soft-misses;
  `FailToVerifyObjWellDefinedResult` also mirrors `Obj`
- Success child evidence stores `Vec<Box<ObjWellDefinedProof>>` (subject is on
  each nested proof; no separate `(Obj, proof)` pair)
- `Err(...)` only for real runtime / invariant failures

Requirement search aggregators return soft fail variants on exhaustion; they
must not emit `Err(RuntimeError::InternalBug)` for “no proof found”.

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
`VerifyObjWellDefinedResult::Success(ObjWellDefinedProof::ByKnown { obj, .. })`.
Both Success proofs and `Failed { obj, reason }` carry the subject `Obj`.
Nested Success child evidence is `Vec<Box<ObjWellDefinedProof>>` (subject lives on each proof).

Atomic-except-equality search is:

builtin rule → known atomic → builtin strategy → by definition →
known strategy → known forall → builtin algebraic rewrite → known algebraic rewrite.

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

The same assume-after-WD pattern applies when *checking* WD of:
`prop` body facts, `exist`/`exist!` body facts, and binder lists (FnSet /
AnonymousFn `dom_facts`, SetBuilder facts) — earlier facts are stored in the
local binder env before later WD so domain-restricted applications can pass.

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
equal search with `VerifyState::known_only_no_wd()` (builtin entry disabled,
no deep phase, no rewrite, no WD store; certificate type
`StrictEqualArgProof`). Nested param occurrences inside compound objs are
bound during that structural recursion. Exist apply also instantiates the
conclusion and alpha-compares to the goal before instantiation requirements.

`VerifyState` non-equality atomic search phases (after WD):

1. **By known**: `search_atomic_except_equality_fact_proof_by_known` first
   tries stored atomic facts, then the object-keyed special-property fact index. It returns
   the existing `AtomicExceptEqualityFactSearchedProof` variants directly:
   `ByKnownAtomicFact` or `ByKnownSpecialProperty`. Both ordinary truth search
   and strategy known-first use this entry; neither needs builtin entry
   or consumes strategy depth.
2. **Builtin rule**: enter when `can_use_builtin_rule` is true. The shared
   `verify_builtin_rule_premise` entry disables ordinary builtin, deep and
   rewrite search for premise truth. Direct known-citation and calculation
   leaves remain available. One checked function-body substitution may finish
   by known equality or calculation; it cannot unfold another definition.
   Premise WD inherits the caller's permissions without storing WD.
3. **Deep**: when enabled, try bounded builtin/user strategies, prop
   definition, known forall, then enabled builtin/known rewrites. The independent
   `remaining_deep_search_depth` starts at 3 and is decremented by
   `after_deep_search()`. Strategy children use their own depth budget (16)
   and cannot enter definition, forall or rewrite search.

Equality retains its own identity / builtin / equality-class / constructor /
deep pipeline; both pipelines share the builtin-entry permission and premise policy.

The [builtin-entry verification receipt](builtin_entry_verification.md) records
the migration boundary, runnable tracer, and release comparison results.

`ByKnownSpecialProperty` reads only exact-object rows from
`special_properties`, across visible environments. It never
writes that table, verifies a premise, or invokes general equality search.
The supported leaves establish function-application codomain or `fn_range`
membership after caller-owned WD. Return sets are structurally substituted
and matched by identity or stored equality paths. Cached WD does not identify
its selected signature, so the leaf declines when visible signatures that
could supply application WD disagree on the required return; bounded strategy
remains available to prove additional domain premises and records its selected
signature citation alongside those premise proofs. Source rows are never
borrowed from an equal function's object key.

`SpecialProperty::Membership(InFact)` and `Equality(EqualFact)` retain the
actual source facts and are indexed centrally by `store_atomic_fact`, regardless
of whether the source is a definition, a proved statement, an inferred fact,
or a local hypothesis. Membership rows use the element's canonical ObjIR;
equality rows use both endpoints. Repeated storage and scope merge deduplicate
identical rows. `cite_property_fact_id` resolves to the source fact, which may
be membership or equality rather than a definition statement.

Function WD collects visible signatures through stored equality neighbors and
records the head-to-signature-subject generating-edge path alongside the source FactId.
Function-body reduction independently follows a known generating-edge path to
an anonymous function and records that path as `function_equal` before checking
the substituted residual equality. Thus `have fn f(x R) R = x + 1; let g = f`
supports `g(4) = 5` directly. A bare `g $in fn(x R) R` qualifies the call but
does not supply a body or prove a particular value.

`DefaultStructView(InFact)` labels the view explicitly selected by a typed
definition. An ordinary later struct membership is indexed as Membership only:
it neither selects default field names nor releases struct laws. Sequence
memberships remain real indexed facts rather than definition-only shape rows.
Statement failure discards all three property kinds with its temporary env;
known-property queries remain read-only and retain their existing search permissions.

Fixed cite-only builtin premises use
`lookup_atomic_except_equality_fact_proof_by_known`: stored atomic facts first,
then the same special-property leaf. Its stored matching uses identity and
stored equality paths only; it cannot enter WD, constructor congruence, peer
comparison, or truth search. `AtomicExceptEqualityFactKnownProof` retains the
queried fact and selected existing searched-proof variant. Detailed output
preserves this nested evidence instead of fabricating a FactId for a property
match. Ordinary known-atomic search retains its existing equality argument
matching and candidate order.

Candidate discovery still owns family/index-union witnesses, subset
intermediates, order edges, and forall parameter completion. Exact source-ID
and history access remain separate. WD, equality unfolding and explicit
commands retain their existing definition-memory readers. The builtin
anonymous-function `fn_range` rule remains a structural rule; the two
named-function definition-memory builtin leaves have been removed.

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
