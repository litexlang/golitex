# Scoped execution state

`ExecEnv` owns one scope's definitions, facts, exact-object properties and WD
records. A child reads its ancestors and writes locally. Successful statements
merge their child; failed statements discard it. Proof-local environments stay
with their existing results and are not implicitly merged.

## Classified exact-object properties

`special_properties` maps an exact `ObjIR` to `ObjectSpecialProperties`:

```rust
pub struct ObjectSpecialProperties {
    pub memberships: Vec<InFact>,
    pub default_struct_views: Vec<InFact>,
    pub equalities: ExactEqualityIndex,
    // Private source-order slots preserve mixed signature-source priority.
}

pub struct ExactEqualityIndex {
    pub ordered: Vec<EqualityEndpoint>,
    pub by_shape: HashMap<EqualToObjShape, Vec<usize>>,
}

pub struct EqualityEndpoint {
    pub fact_id: FactId,
    pub value_side: EqualitySide,
}
```

Equality buckets hold citations and endpoint directions; the original
`EqualFact` remains in that scope's `facts_by_id`. A resolved `SpecialProperty`
is a source-fact view used by existing signature/proof consumers, not the stored
mixed-vector layout.

The bucket key is the opposite endpoint's outer constructor:

- Function values and spaces: `AnonymousFn`, `FnSet`.
- Finite values and products: `Tuple`, `Cart`.
- Individual set constructors: `SetBuilder`, `ListSet`, `Range`, `ClosedRange`,
  `SeqSet`, `FiniteSeqSet`, `PowerSet`, `Preimage`, `PreimageSet`.
- Other structured expressions used by readers: `FnObj`,
  `InstantiatedTemplateObj`, `FieldAccess`.
- `Other` retains all remaining direct endpoints for generic equality lookup.

There is no `SetStructure` bucket. Classification is structural, not a proof
that an object belongs to a mathematical type. In Litex's pure-set model,
function values and numerals are sets too. A literal `FnSet` supplies a space;
equality to it alone does not make its alias an applicable function.

## Sources, direction and order

Recording `a = b` indexes the actual source under both exact keys, with `Right`
as the value side for `a` and `Left` for `b`. Both endpoints may be literals.
When their keys coincide, one source FactId is retained and the historical
left-first reader orientation selects the right endpoint. Re-recording a
source is idempotent for this index.

Single-bucket and multi-bucket readers preserve equality insertion order.
Bucket union sorts and deduplicates entry positions, so requesting the shapes
in a different order cannot change source priority. Visible scopes are read
innermost first. Mixed membership/equality signature readers retain their
original property order through the private source-order slots. Merge replays
those slots after mounting their facts, retaining original FactIds and order.
Default struct views remain separately selected by typed definitions; ordinary
struct membership cannot select a field view.

## Query boundaries

The shared runtime helpers live in `execute/execute_fact_stmt/helper.rs`:

```rust
known_equal_to_anonymous_functions(&head)
known_equal_to_tuples(&subject)
known_equal_to_carts(&carrier)
known_equal_to_set_builders(&carrier)
exact_property_object_values_of_shapes(&object, &shapes)
```

The `known_equal_to_*` readers return only direct stored equality candidates
and their one-edge citations. A matching bare literal belongs to the caller's
literal route. `exact_property_object_values_of_shapes` explicitly includes
the matching object itself with an empty path, followed by the selected direct
equality candidates. Both routes retain the historical first-candidate IR
deduplication, including skipping reflexive equality candidates.

The generic `exact_property_object_values` still supports arbitrary direct
endpoints plus the object itself; exact equality/path readers use it without
following equality classes. `f = g` and `g = fn(...) {...}` do not provide a
body to `f`. A proved and stored `f = fn(...) {...}` does. Function membership
provides a signature, not a body. WD, domain, arity, rewrite admission and
residual proof checks remain the consuming rule's responsibility.

## Numeric and ordinary equality indexes

`KnownFactMemory.known_closed_numeric_equal` remains the separate content-based
numeric index. For example, `1 / 2` has an arithmetic outer constructor but is
also a `ClosedNumericExpr`. Exactly one closed side indexes the other side;
both-closed/neither-closed sources are skipped by that numeric index. Numeric
classification does not itself certify WD or guarantee successful evaluation.

`known_equivalence_classes` retains ordinary equality truth/path search. It
does not expand a structural reader's permissions. The old, unread
`known_equal_to_obj_with_free_params` storage/merge index has been removed;
anonymous functions, FnSets and set builders use the same exact shape buckets
as other constructors.

The buckets avoid cloning unrelated equality targets during structural
queries. No latency or universal speedup is claimed: small objects also pay
for the additional bucket metadata and lookup.

Acceptance: [strict tracer](../../examples/proof_nodes/equal/by_object_definition/by_fn_application/classified_exact_properties.lit)
and [index/reader regressions](../../tests/unit/execute/classified_exact_properties/tests.rs).
