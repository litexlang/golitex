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
  and the predicate signature is valid. Fields follow those stages:
  `well_defined_of_each_parameter`, then `predicate_signature`.
- User `prop` / `abstract_prop` signatures resolve through the complete
  `AtomicName`, including module/file ownership, and require exact arity.
  A later declaration inside a proof body cannot define an earlier claim goal.
- `Ok(Failed(Argument(reason)))` when argument Obj WD soft-misses, or
  `Ok(Failed(Predicate { well_defined_of_each_parameter, reason }))` for an
  undefined predicate or wrong arity after the arguments passed.
  Predicate failures are not represented as object failures.
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

Anonymous-function WD always proves `body $in ret_set` in its parameter/domain
scope, including when `body` is a parameter projection. The successful
`AnonymousFnObjWellDefinedProof.body_in_ret_set` field is mandatory, and Detailed
JSON always projects it. `have fn` definitions and anonymous literals share
this check before any function signature is stored. Struct-instance WD uses
`type_facts_for_typed_arguments` to prove substituted header types before
recording a WD id; its existing `requirement_fact_verified` list retains the
argument-type proofs. Failures retain the actual unsatisfied type obligation.

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
Independent `not forall` and `forall … <=>:` WD also assume each checked
domain fact before later domains and conclusions. Only the common domain
guards both iff branches: neither branch is assumed while checking the other.
The binder environment stays in the WD proof and is never merged into the
parent; WD alone does not prove the quantified proposition.

Function-application signature candidates have no binder scope to retain.
Their isolated checks disable new WD-cache storage: returned children and
requirements carry full proofs or cite ancestor-owned ids. After selection,
the caller records the successful application according to its original
`store_well_defined_fact` setting. A failed candidate leaves no WD cache entry.

Known-exist reuse checks WD first, preserves the existing existential-kind
implication gate, and structurally compares typed binders and the complete
body through the existing alpha-equality helpers. Nested function/set binders
may be renamed; their carriers, bodies, predicates and free owners must match.
The shape index and stored citation ownership are unchanged.

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
truth-only equality search at `VerifyStateLevel::Direct` (identity/alpha,
stored paths and closed calculation; certificate type `StrictEqualArgProof`). Nested param occurrences inside compound objs are
bound during that structural recursion. Exist apply also instantiates the
conclusion and alpha-compares to the goal before instantiation requirements.

`VerifyState` now has exactly `level` and `can_rewrite`. Equality and other
atomic facts use one `search_atomic_fact` schedule; family wrappers retain
their own evidence types. `verify_*` checks WD first, whereas `search_*` assumes
the target's WD is already established.

| Target stage | Premise ceiling |
|---|---|
| Direct (0): identity/alpha, stored facts/paths, then closed calculation | No new search |
| KnownSpecialProperty (1) | Direct (0) |
| BuiltinRule (2) | KnownSpecialProperty (1) |
| Strategy (3), including new peer bridges | BuiltinRule (2) |
| DefinitionAndForall (4) | BuiltinRule (2) |
| Rewrite, only at (4, true) | (4, false) |

Family dispatch preserves permissions. Rule admission derives the premise
state once; recursive WD and inference receive that state rather than creating
a new root. Constructor congruence may traverse a finite syntax tree with a
fixed leaf ceiling. Stored alpha paths do not start peer searches.

Exploratory WD returns evidence without recording reusable WD objects. The
existing accepted-fact commit records checked atomic subjects in the current
transaction, excluding named identifiers and quantified binder internals.
A stored atomic fact can supply its predicate-domain evidence by an explicit
citation, after argument WD and visible predicate signature checks.

Direct is implemented by `search_atomic_fact_proof_by_known_fact_or_closed_calculation`,
returning `DirectAtomicFactSearchResult::{ByKnownFact, ByClosedCalculation, NotFound}`.
The closed calculator is a pure free function with no Runtime or state parameter.
It supports classified closed decimals, exact rational/complex values, real order
and standard-set membership/non-membership; symbolic normalization, constructor
shape calculations and user definitions retain their existing higher routes.
The existing `lookup_known_*` interfaces remain citation/identity only.
Detailed output retains `by_closed_calculation` and exact values, rather than
labelling computed proofs as citations or builtin rules.
See the [verification receipt](builtin_entry_verification.md) and
[Direct tracer](../../../examples/proof_nodes/equal/direct_closed_calculation.lit).
Remaining composition and geo failures are tracked separately.
No independent strategy/deep depth budget remains.

The function codomain/range leaves of `ByKnownSpecialProperty` read exact-object rows from
`special_properties`, across visible environments. The shared tuple reader
also follows cited stored equality paths for object and Cartesian aliases. It never
writes that table, verifies a premise, or invokes general equality search.
The function leaves establish function-application codomain or `fn_range`
membership after caller-owned WD. Return sets are structurally substituted
and matched by identity or stored equality paths. Cached WD does not identify
its selected signature, so the leaf declines when visible signatures that
could supply application WD disagree on the required return; bounded strategy
remains available to prove additional domain premises and records its selected
signature citation alongside those premise proofs. Source rows are never
borrowed from an equal function's object key.

Known tuple structure supplies ordered reconstruction and coordinate/length
equalities, plus the atomic tuple, bound, and coordinate-carrier requirements
of projection WD. Function-coordinate equality uses one body substitution;
all candidate WD signatures must agree with that body's full signature.
These success certificates retain source paths and signature matches. They
are transient, do not extend the fact store or WD cache, and never call the
bottom-level equality lookup recursively. See the equality directory README
and `examples/proof_nodes/equal/by_known_special_property/`.

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

## Exact whole-forall source replay

`verify_forall_fact` first compares the goal against whole stored forall facts
in the existing live env stack. A structural match renames outer binders
positionally and uses the existing existential alpha key for witness binders;
carriers, premises, fact polarity and free owner identities remain exact.
The verifier checks the full goal WD before returning `ByKnownForallFact`
with a real source FactId and parameter renamings. An unused parameter is
never instantiated with a default term. This exact citation does not enter
deep forall-pattern search or consume its budget.

On a miss, the existing local-introduction pipeline remains: introduce typed
parameters, assume checked domains, then prove and locally store conclusions.
Both routes retain their WD/local environments in typed evidence. Nested
forall/anonymous-function alpha equivalence is not added by this exact-source
matcher; those shapes retain their ordinary verification routes.

The stable tracer is `examples/stmt_nodes/definition/forall_source_replay.lit`;
producer/consumer and failure boundaries are in
`tests/unit/execute/forall_source_replay/tests.rs`. Imported exist! theorem
fixtures currently use source fallback because their facts are outside the
existing KB codec subset. Supported cached definitions are tested separately.

Builtin predicate domain WD checks carriers before admitting an assumption.
Domain proof search retains its caller's budget and may cite stored equality
paths, but does not expand equality peers: a function peer's binder WD can
otherwise infer another order fact and reopen the same domain obligation.
When ordinary search misses after completed WD, calculation/citation leaves
reuse that evidence without restarting WD or proving the enclosing predicate. Function
properties first try the exact FnSet membership; alternatives cite the actual
declared signature and prove domain/codomain equalities. The legacy
`fn(k N+: k <= n) B` prefix is admitted only on `closed_range(1,n)` with both
endpoint equalities proved. Other restricted domains retain their rejection
boundaries.
