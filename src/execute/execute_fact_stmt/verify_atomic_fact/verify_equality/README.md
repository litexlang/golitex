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
   is available even when builtin fuel is zero.
3. Mathematical identities and calculation belong to `ByBuiltinRule` and retain
   their existing fuel requirements.
4. Stored equality gives alternative objects on which those checks may work.
   One `ByEquivalenceClass` stage first looks for an entirely stored path, then
   tries one cheap comparison between members of the two endpoint classes.
5. Every stored step needs its generating equality's `FactId`; every new step
   needs its own proof. A shared class handle is a search index, not evidence.
6. These are search changes. `exec_stmt` still owns statement transactions, and
   the existing fact-statement pipeline stores and infers only after verification.

## Entry and search order

```text
verify_equal_fact(goal, state)
  -> WD left, then right
  -> search_equal_fact_proof(goal, state)
       -> ByTheyAreTheSame
       -> ByBuiltinRule (if the caller has builtin fuel)
       -> ByEquivalenceClass
            -> stored path
            -> peer comparison (if permitted)
       -> existing tail:
            restricted state: Matching -> miss
            full state: ObjectDefinition -> Strategy -> Matching
                        -> KnownForall -> Rewrite -> miss
```

The strategy subtree has its own existing entry in `verify_in_strategy.rs`.
It also checks `ByTheyAreTheSame` first, then keeps its existing cite-only /
calculation builtin entry, unified class search, and nested strategy order.
Moving identity out of builtin must not remove it from this second entry.

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

The bridge runs WD, then identity, budgeted builtin, or constructor matching.
It never starts object-definition, strategy, forall, or rewrite search. It
inherits the caller's fuel instead of obtaining a fresh top-level budget.
At zero builtin fuel, identity and matching remain available.

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
and successful statement results. Focused Rust tests check zero-fuel identity,
free-variable and domain boundaries, WD rejection, oriented multi-edge paths,
both peer sides, inherited fuel, no nested peer expansion from matching,
unchanged caller stores, and Normal/Detailed provenance.

The [verification record](verification.md) gives the exact baseline, measured
coverage, remaining failures, and current CLI/harness limitations.
