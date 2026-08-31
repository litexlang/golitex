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
    pub predicate_algebraic_properties: EnvironmentPredicateAlgebraicPropertyStore,
    pub caches: EnvironmentVerificationCache,
}
```

The type itself lives in [`environment.rs`](environment.rs). Module declarations
and public re-exports live in the wiring-only [`mod.rs`](mod.rs). Feature logic
is organized by the current owner and field names:

```text
environment.rs                                                   the five Environment owners and construction
definitions/definitions.rs                                       reusable name definitions
facts/facts.rs                                                   fact-owner composition root
facts/                                                            fact records and typed search indexes
object/object.rs                                                 canonical object owner
object/                                                          reusable facets known about one object
predicate_algebraic_properties/predicate_algebraic_properties.rs predicate-name property owner
predicate_algebraic_properties/                                  property profile and registration operations
caches/caches.rs                                                 reusable environment-scoped verification results
display.rs                                                       Environment formatting
merge.rs                                                         committed-child transaction
```

The main Environment and every direct owner entry deliberately repeat their
parent folder name: `environment/environment.rs`,
`definitions/definitions.rs`, `facts/facts.rs`, `object/object.rs`,
`predicate_algebraic_properties/predicate_algebraic_properties.rs`, and
`caches/caches.rs`. Each owner directory has a wiring-only `mod.rs`; supporting
files name narrower responsibilities. A larger operation may have one file
whose helper functions are branches of that operation; for example,
`facts/storage.rs` is the central fact-storage dispatch.

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
| `predicate_algebraic_properties` | One predicate-name entry whose profile independently records transitivity, symmetry permutations, reflexivity, and antisymmetry. |
| `caches` | Environment-scoped verification results reusable by later statements: well-defined object results and infer-rule firing guards. |

Definitions retain symbol identity, not the syntactic construct that first
introduced a name. `EnvironmentDefinitionRegistry` owns a `SymbolTable`; each
entry has a globally allocated `SymbolId` and only the coarse `SymbolRole`
needed for namespace/conflict rules. There is no `ParamObjType` table for
remembering whether an object came from `forall`, `exist`, a function set, or
another binder form. Alpha-renaming is implemented by `SymbolId`-keyed
substitution and therefore does not depend on those declaration-site kinds.

`EnvironmentFactStore` is itself a composition root rather than a flat list of
maps:

| Fact owner | Canonical responsibility |
| --- | --- |
| `known_equality` | Equality classes and exact proof paths. |
| `atomic` | Atomic facts separated by argument arity. |
| `set_relations` | Direct membership and inclusion edges. |
| `quantified` | Stored existential and disjunctive facts. |
| `forall_conclusions` | Conclusions projected from exact stored universal facts, including argument-shape lookup. |
| `stored_facts` | Canonical `FactId` records and proposition lookup aliases. |

Statement-local memoized proofs and recursive proof-search guards do not belong
to these five stores. They live in Runtime's statement proof context and are
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
- failed or discarded child environments are not merged.

The primary regression tracer is
[`examples/03_language_features/idempotent_template_child_environment_reuse.lit`](../../examples/03_language_features/idempotent_template_child_environment_reuse.lit).
It checks the important boundary where template-instantiation support is made
inside a child environment and must remain reusable after the child commits.
The example is intentionally standalone rather than registered in a local
`litex.config`, so run it with:

```bash
target/release/litex -isolated -graph -f examples/03_language_features/idempotent_template_child_environment_reuse.lit
```

## Well-definedness preflight changes

A quantified theorem or claim may materialize sound support while checking the
well-definedness of its conclusions. That support is returned as
`WellDefinednessEnvironmentDelta`, not as a second queryable `Environment`.
The delta has the same five private ownership categories only so it can preserve
the exact checked changes. Its public operations are intentionally limited to:

```rust
delta.merge_committed_environment(checked_child)?;
delta.apply_to(real_environment)?;
```

This makes the algorithmic boundary match the data structure: proof code can
replay checked changes, but cannot accidentally ask a partial certificate what
the complete world knows.

Start with [`environment.rs`](environment.rs) for the five owners,
[`merge.rs`](merge.rs) for child commit,
[`facts/facts.rs`](facts/facts.rs) for the fact composition root,
[`object/object.rs`](object/object.rs) for the keyed object profile, and
[`well_definedness_environment_delta.rs`](well_definedness_environment_delta.rs)
for WD replay.

## Migration verification

The ownership boundary is checked at both structural and behavioral levels:

- the source-architecture test requires the five direct fields, matching owner
  paths, five typed fact owners, one object map, one predicate-profile map,
  private WD-delta fields, and the absence of the retired path vocabulary plus
  the old repository/Deref facade and `environment_state.rs`;
- Environment merge regressions exercise successful child commits and rejected
  conflicts;
- the user-strategy tracer confirms that a checked strategy publishes its
  `forall` into the ordinary fact store without a separate activation owner.
