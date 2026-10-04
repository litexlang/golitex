# Equality verification

This directory owns equality WD and proof search. The entry remains
`Runtime::verify_equal_fact`; it returns the existing `VerifyFactResult::Equality`
wrapper. No new AST fields, environment store, runtime cache, or class index are
needed for identity and peer comparison.

## Derivation and responsibilities

1. A goal must refer to well-defined objects before equality can establish
   anything. `verify_equal_fact` therefore checks both sides before truth search.
2. Equal IR and structural alpha equality identify the same object without a
   mathematical rule or a stored fact. They belong to `ByTheyAreTheSame`, which
   is available even when builtin entry is disabled.
3. Already stored equality paths are read before mathematical rules or
   structural-property inference. They keep `ByEquivalenceClass::KnownPath`
   evidence and start no new proof search.
4. Mathematical identities and calculation belong to `ByBuiltinRule` and retain
   the caller's builtin-entry permission.
5. Stored equality also gives alternative objects on which those checks may work.
   The later `ByEquivalenceClass` fallback handles alpha endpoints and
   restricted comparison between members of the two endpoint classes.
6. Every stored step needs its generating equality's `FactId`; every new step
   needs its own proof. A shared class handle is a search index, not evidence.
7. These are search changes. `exec_stmt` still owns statement transactions, and
   the existing fact-statement pipeline stores and infers only after verification.

## Entry and search order

```text
verify_equal_fact(goal, state)
  -> WD left, then right with the same ceiling
  -> search_equal_fact_proof -> shared search_atomic_fact
       0 identity/alpha, stored paths/facts
       1 special properties and finite constructor descent (leaves 0)
       2 builtin rules (premises 1)
       3 strategies and searched peer bridges (premises 2)
       4 object definitions and known forall (premises 2)
       rewrite at (4,true) -> residual at (4,false)
```

There is no separate strategy search state or depth budget. A pure stored
alpha-path citation belongs to level 0; a newly proved peer bridge belongs to
level 3 and cannot reenter that stage.
The [stored-equality priority tracer](../../../../../examples/proof_nodes/equal/by_equivalence_class/stored_equality_before_builtin.lit)
releases the geo dot-symmetry theorem and reads its exact conclusion.

## Known tuple properties

`ByKnownSpecialProperty` is a sibling of identity, not another alpha case.
Cartesian membership proves `p = (p[1],p[2])`; a stored path to `(a,b)` proves
`p[1] = a`. A function definition may supply a literal tuple after one beta
substitution. Application WD precedes this step, and all candidate WD
signatures must agree with the selected definition's full signature, including
domains. A signature ambiguity or non-tuple body misses without recursive
unfolding. Checked template declarations participate through equality aliases:
the declaration signature and every competing stored/template signature must
agree. `FnTupleValue` reads one tuple-valued application reached by a stored
subject path, and `FnTupleProjection` can use that path for a named result.
Neither route publishes a value equality or restarts definition search. See
[the template alias tracer](../../../../../examples/stmt_nodes/definition/template_alias_struct_tuple.lit).
Tuple shape also supplies atomic `is_tuple`, literal index bounds,
coordinate carrier membership, and equality `tuple_dim(p) = n`.

The shared reader in `known_tuple.rs` only traverses stored equality edges
with visited-node tracking. It retains FactIds and local certificates, writes
no facts or WD, and never calls a verifier. The bottom-level
`lookup_known_obj_equality` stays identity/stored-path-only. Both ordinary and
strategy equality entries, strict argument conversion, and Detailed JSON
retain the new route. See the runnable
[reconstruction](../../../../../examples/proof_nodes/equal/by_known_special_property/tuple_reconstruction.lit),
[projection](../../../../../examples/proof_nodes/equal/by_known_special_property/tuple_projection.lit),
and [function projection](../../../../../examples/proof_nodes/equal/by_known_special_property/fn_tuple_projection.lit)
tracers.

## Identity: two cases

`by_they_are_the_same/` contains a pure comparison, success evidence, and the
existing alpha-comparison helper moved out of the builtin directory.

```text
TheyAreTheSameProof
  SameIr
  SameFreeParamShape
    FnSet
    AnonymousFn
    SetBuilder
```

Alpha comparison maps bound identifiers and checks parameter types, domain
facts, return types, and bodies under that mapping. Free identifiers retain
their identity. It does not reorder conditions, unfold names, query known
facts, or prove mathematical equivalence between different bodies.

## One equivalence-class stage

`search_equal_fact_proof_by_equivalence_class` builds one local snapshot of the
visible generating-edge graph. It first searches for a stored path connecting
the goal endpoints. If that fails and peer comparison is allowed, BFS collects
one oriented path to each distinct IR member of each class. Candidates are
tried in this order: left-only, right-only, then both endpoints replaced.
Each list includes its starting object; the unchanged goal pair is skipped.
Stored edge order makes candidate selection deterministic.

```text
goal: a = c

KnownPath:
  a --stored FactId--> ... --stored FactId--> c

ViaPeers:
  a --stored path--> b --checked bridge--> d --stored path--> c
```

The second form supports two aliases whose literal FnSet members differ only
by bound names. The right BFS runs from `c` to `d`; the returned proof reverses
both edge order and direction to certify `d` to `c`.

The bridge runs WD, then identity, permitted builtin, or constructor matching.
It never starts object-definition, strategy, forall, or rewrite search. It
inherits the caller's builtin permission.
With builtin entry disabled, identity and matching remain available.

`VerifyState::for_equality_peer_comparison` sets
`EqualityClassSearchMode::StoredPathsOnly`, disables deep search and rewrite,
and disables WD storage. All child state transitions preserve this mode.
Matching children may cite existing equality paths and recurse through smaller
constructors, but may not launch another peer comparison. Builtin premises and
direct bridge WD obligations inherit the same restriction. Search never stores
the bridge or merges the two classes in the caller's knowledge base; only the
normal successful statement can store its goal.

This is a verifier-state restriction, not a global inference policy. Binder WD
still opens its existing local environment, introduces parameter/domain facts,
and runs local inference. `try_store_inferred_fact_and_infer` and the positive
real-power inference rule create their own `VerifyState`; those separate entries
do not inherit the bridge restriction. Their local facts remain scoped to the
WD proof. Preserving this boundary avoids changing the store/infer architecture
in this update. A ban on peer expansion throughout all inference would require
a separate policy-propagation change; this implementation does not claim it.

There is no arbitrary peer-count cutoff. At most the product of the two class
sizes is considered. Direct verifier children cannot repeat peer expansion;
this is not a termination guarantee for the whole inference system. Large
classes may still be expensive.

## Result mirrors the proof

```text
VerifyEqualityResult
  Failed: WD failure | search failure
  Success
    fact
    well_defined_proof
    searched_proof: EqualFactSearchedProof
      ByTheyAreTheSame(...)
      ByBuiltinRule(...)
      ByEquivalenceClass: EqualFactSearchedProofByEquivalenceClass
        KnownPath: KnownEqualityPathProof
          path: [(from, to, FactId)]
        ViaPeers: EqualityViaPeersProof
          left_path
          bridge: PeerEqualitySuccess
            fact
            well_defined_proof
            searched_proof: identity | builtin | matching
          right_path
      ... existing routes
```

An empty stored path means its endpoints are the same object. Only successful
proofs enter `searched_proof`; failed candidates are not mixed into evidence.
`RuntimeResult::Err` continues to mean an operational/invariant failure.

## Membership uses the same equality interface

```litex
let g = fn(x R) R
have fn f(t R) R = t
f $in g
```

`ByKnownAtomicFact` selects the stored `f $in FnSet(t)` and proves its arguments
equal to the goal arguments. `f = f` uses `SameIr`. `FnSet(t) = g` uses
`ViaPeers`: compare `FnSet(t)` with the stored `FnSet(x)` by alpha identity,
then cite the stored `FnSet(x) = g` edge. No membership-specific alpha rule is
needed. Both endpoint peers are also needed for `g = h` when both are aliases.

The old free-param lookup builtin is removed from truth search. The existing
`known_equal_to_obj_with_free_params` index and its storage/merge contracts are
retained; removing that state is a separate migration. Ordinary stored equality
edges already provide the needed shapes and complete citation paths.

## Output and checks

Normal JSON reports identity as `they_are_the_same` and class proofs as
`equivalence_class`. Detailed JSON uses `by_they_are_the_same` with `kind` and
optional `shape`, or `by_equivalence_class` with `kind: known_path | via_peers`.
The latter keeps both paths and the bridge's WD and truth proof. Known-atomic
Detailed output also preserves each parameter's equality proof, so the above
membership explanation includes its complete transport chain.

The maintained acceptance file is
[`peer_alpha_membership.lit`](../../../../../examples/proof_nodes/equal/by_equivalence_class/peer_alpha_membership.lit).
It preserves the rejected baseline in comments and uses no trust. Run:

```sh
cargo test --release equality_search_tests -- --nocapture
target/release/litex -strict -f examples/proof_nodes/equal/by_equivalence_class/peer_alpha_membership.lit
```

The CLI gate requires exit 0, top-level `success: true`, no `session_error`,
and successful statement results. Focused Rust tests check identity with builtin entry disabled,
free-variable and domain boundaries, WD rejection, oriented multi-edge paths,
both peer sides, inherited builtin permission, no nested peer expansion from matching,
unchanged caller stores, and Normal/Detailed provenance.

## Exact numbers and aggregates

Number construction, parsing and persisted-number decoding share exact decimal
normalization. Guarded complex calculation retains proofs of every nonzero
denominator, including the imaginary-unit builtin. Finite aggregate calculation
shares the display evaluator, but algorithm terms must cite a checked function
equation before contributing equality evidence. The evaluator checks function
applications, substitutes by binding identity and records each fold step. Nested
aggregates share a 1024-term allowance, checked integer bounds and a depth limit.
Failed evaluation returns no equality evidence; `eval` publishes no fact.

Symbolic aggregate identities are separate premise-bearing rules. They retain
range legality, function coverage, pointwise comparisons or adjacency/disjointness
as appropriate. Detailed output projects each dedicated rule and its supporting
evidence. The maintained tracers are `examples/proof_nodes/equal/by_builtin_rule/`
`numeric_normalization.lit`, `imaginary_division.lit`,
`aggregate_calculation.lit` and `aggregate_identities.lit`.

The [verification record](verification.md) gives the exact baseline, measured
coverage, remaining failures, and current CLI/harness limitations.


## Exact numeric and periodic leaves

`rational_expression::exact_rational` owns checked signed integer powers and
closed rational arithmetic; calculation retains `ClosedRational` normal forms.
Order predicates share `compare_closed_numeric_objs`, with the existing decimal
path followed by exact positive-denominator comparison. Whole-fact WD precedes
these leaves, so normalization cannot cancel an unproved zero denominator.

The existing trig/complex builtin family consumes two local producers:
`by_periodic_trig` splits a syntactic pi coefficient into an exact constant and
linear symbolic terms, reduces the constant modulo the mathematical period and
checks each surviving integer term through `verify_builtin_rule_premise` using
inherited state. Its sine/cosine nonzero certificate independently supplies
tangent/cotangent WD. It neither increases recursion budgets nor adds facts.
`by_numeric_complex_modulus` consumes exact numeric coordinate arithmetic and
checks the nonnegative principal root against the squared modulus. Detailed
and Normal projections consume the same winning proof payloads.

The primary tracer is
`examples/proof_nodes/equal/by_builtin_rule/periodic_trig_exact_values.lit`.
Paired pole, noninteger-period, zero denominator and negative-root controls are
in `examples/negative/exact_numeric_periodic_modulus/`. This checkout contains
no active Lean compiler under `src/`; these additions make no Lean replay claim.

### Direct calculation at level 0

`search_atomic_fact` first consumes `DirectAtomicFactSearchResult`. Raw equality
lookup still returns identity/alpha or stored paths. A new closed numeric hit
becomes `EqualFactSearchedProof::ByClosedCalculation`, also supported by
`StrictEqualArgProof`, with exact normal forms/coordinates retained in Detailed
JSON. Symbolic `Rational`/`Complex` normalization stays in the builtin stage.
The pure calculator does not read known numeric representatives or unfold
functions; WD remains a separate mandatory stage at the caller's ceiling.

Function-definition normalization preserves an exact single-application beta
step before normalizing symbolic arguments. For example, a square function
can prove `outer(inner(x)) = inner(x)*inner(x)` without expanding `inner`.
The exact match only selects where expansion stops: the named call and the
selected anonymous body's own domain must both pass WD, and the existing
normalization certificate retains both checks and the body source. Other
targets continue through the bounded argument/body normalization route.
See `examples/proof_nodes/equal/by_object_definition/nested_call_one_step.lit`
and the positive, guarded-body and invalid-argument function-body tests.

The elementary closed producers additionally support fraction rounding/sign,
integer operations on exactly integral expressions, perfect rational roots,
bounded square-free radical arithmetic, rational complex projections and rational
logarithms via exact prime valuations. `ClosedValuePair::Radical` retains both
canonical objects in Detailed output (`representation: radical`); Normal keeps
the existing closed-calculation explanation. Radical order and general radical
field inversion are not added. Pure leaf tests separately retain symbolic,
undefined and exhausted misses; public statement tests check WD and display
evaluation. See `tests/unit/execute/closed_exact_elementary_calculation/tests.rs`
and the four `closed_*_calculation.lit` tracers.
