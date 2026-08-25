# Mathematical environment

`Environment` is the persistent mathematical world visible to later Litex
statements. It is not a bag of temporary proof-search state and it is not a
one-field wrapper around another object.

The ownership boundary is visible directly in Rust:

```rust
pub struct Environment {
    pub definitions: EnvironmentDefinitionRegistry,
    pub facts: EnvironmentFactStore,
    pub objects: EnvironmentObjectKnowledgeStore,
    pub predicate_properties: EnvironmentPredicatePropertyStore,
    pub caches: EnvironmentVerificationCache,
    pub strategies: EnvironmentStrategyRegistry,
}
```

Before this split, callers saw `Environment { repositories }` and relied on
`Deref` to reach roughly forty unrelated maps. That hid which subsystem owned
each lookup and made a partial environment look like a meaningful abstraction.
There is now no `EnvironmentPersistentRepositories` and no compatibility
`Deref`.

## What each field owns

| Field | Canonical responsibility |
| --- | --- |
| `definitions` | Symbol identity and definitions of objects, predicates, algorithms, structs, templates, settings, theorems, axioms, and strategies. |
| `facts` | Stored `FactId` records plus equality, membership, quantified-fact, and argument-shape indexes used to find them. Search indexes remain here because they are maintained with the fact store. |
| `objects` | One `ObjString -> EnvironmentObjectKnowledge` entry per object key. Tuple/cart shape, sequence or matrix shape, simplified value, set-builder equality, and function-set knowledge are optional facets of that one entry. |
| `predicate_properties` | One predicate-name entry whose profile independently records transitivity, symmetry permutations, reflexivity, and antisymmetry. |
| `caches` | Environment-scoped verification results reusable by later statements: well-defined object results and infer-rule firing guards. |
| `strategies` | One atomic-fact-family entry with an `Active` or `Stopped` state and the selected strategy name. |

Statement-local memoized proofs and recursive proof-search guards do not belong
to these six stores. They live in Runtime's statement proof context and are
discarded with that statement/local scope.

## Example: storing and later reusing a fact

After Litex checks `have a R = 1`, execution updates several owners, but each
piece has one clear home:

```text
store checked fact `a = 1`
  definitions: resolve the SymbolId of `a`
  facts:        allocate/store FactId f3 and equality/search indexes
  objects:      remember the simplified value of `a` in a's knowledge profile
  caches:       remember only environment-valid reusable checks

later goal `a + 1 = 2`
  facts + objects provide the exact stored equality/value evidence
```

The data is grouped by owner, not forced into a single enum: definition and
fact payloads are heterogeneous, while object and predicate knowledge genuinely
share one stable key and therefore use one keyed profile.

## Local environments and commit

Proof blocks, `try`, template materialization, and other local executions build
a child `Environment`. A successful child is committed by
`Environment::merge_committed_child`:

- definition conflicts are rejected before mutation;
- fact indexes and exact `FactId` records are merged;
- all facets for the same object or predicate key are combined;
- the child's final strategy state overrides the same key in the parent;
- failed or discarded child environments are not merged.

The primary regression tracer is
[`examples/03_language_features/idempotent_template_child_environment_reuse.lit`](../../examples/03_language_features/idempotent_template_child_environment_reuse.lit).
It checks the important boundary where template-instantiation support is made
inside a child environment and must remain reusable after the child commits.

## Well-definedness preflight changes

A quantified theorem or claim may materialize sound support while checking the
well-definedness of its conclusions. That support is returned as
`WellDefinednessEnvironmentDelta`, not as a second queryable `Environment`.
The delta has the same six private ownership categories only so it can preserve
the exact checked changes. Its public operations are intentionally limited to:

```rust
delta.merge_committed_environment(checked_child)?;
delta.apply_to(real_environment)?;
```

This makes the algorithmic boundary match the data structure: proof code can
replay checked changes, but cannot accidentally ask a partial certificate what
the complete world knows.

Start with [`environment_state.rs`](environment_state.rs) for the six owners,
[`environment_merge.rs`](environment_merge.rs) for child commit,
[`object_knowledge_store.rs`](object_knowledge_store.rs) for the keyed object
profile, and
[`well_definedness_environment_delta.rs`](well_definedness_environment_delta.rs)
for WD replay.

## Migration verification

The ownership migration was checked at both structural and behavioral levels:

- the source-architecture test requires the six direct fields, one object map,
  one predicate-profile map, one strategy-state map, private WD-delta fields,
  and the absence of the old repository/Deref facade;
- all Environment merge tests and all 21 strategy-filtered regression tests
  pass;
- the isolated primary tracer returns runner `ok: true`;
- the examples/docs harness passes all 122 selected example groups and every
  extracted Litex documentation snippet;
- the release all-target suite passes when excluding five concurrent
  structured-integer-induction compiler tests whose fixture is rejected by the
  current parser before Environment execution begins. Those five all report
  the same `induc ? from` same-line parse error and are outside this ownership
  migration; the remaining 1136 library tests and every integration target,
  including all 17 public showcases, pass.
