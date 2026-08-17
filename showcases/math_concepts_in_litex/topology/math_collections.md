# Mathematical Collections: Topology

## Purpose and scope

This standalone first version models topologies as collections of open sets
and proves a short theorem chain through named settings. It targets readers
who know elementary sets and functions. Bases, filters, compactness,
connectedness, separation, and quotient constructions are outside this
checkpoint.

## Modeling conventions

For a carrier `X`, a candidate topology is an ordinary value in
`power_set(power_set(X))`. Native `intersect`, `union`, `big_union`, set
builders, subset, and function application are reused directly. Candidate
properties remain relations with explicit parameters; settings abbreviate
only universal theorem contexts.

## Mathematical spine

### Candidate topology

- **Ordinary meaning:** a collection containing the empty set and whole
  carrier, closed under binary intersections and arbitrary unions.
- **Semantic role:** Relation testing a supplied collection.
- **Ideal Litex form:** `prop is_topology_on(X, T)`.
- **Interface sketch:** `T power_set(power_set(X))` with the standard axioms.
- **Nearest wrong alternative:** A new topology object or custom union
  construction would duplicate native set objects and operations.
- **Dependencies:** Power sets, intersection, `big_union`, and subset.
- **Downstream uses:** `TopologicalSpaceSetting` and open-set closure laws.
- **Allowable hole:** None in the first checkpoint.

### Topological theorem setting

- **Ordinary meaning:** reason in an arbitrary supplied topological space.
- **Semantic role:** Reusable universal theorem context.
- **Ideal Litex form:** `setting TopologicalSpaceSetting` with `X`, `T`, and
  the topology laws written directly. The first-class `is_topology_on(X,T)`
  proposition remains the definition-facing interface.
- **Interface sketch:** `forall [TopologicalSpaceSetting], U, V T: ...`.
- **Nearest wrong alternative:** A struct forces field projection even when
  no theorem passes a topological space as a value.
- **Dependencies:** Candidate topology.
- **Downstream uses:** Binary open unions and three-way open intersections.
- **Allowable hole:** Settings cannot define or return a topology. The current
  elaborator also cannot replay a proposition call from a setting into a
  theorem header, so the theorem-facing setting repeats the laws directly.

### Continuity

- **Ordinary meaning:** every open set in the codomain has open preimage.
- **Semantic role:** Relation on two candidate topologies and a function.
- **Ideal Litex form:** `prop is_continuous(...)` plus a named composition
  setting.
- **Interface sketch:** topology facts for source and target followed by
  `forall V T_Y: {x X: f(x) $in V} $in T_X`.
- **Nearest wrong alternative:** A continuous-map struct is premature before
  callers pass or project packaged maps.
- **Dependencies:** Candidate topologies, functions, and set builders.
- **Downstream uses:** Composition of continuous functions.
- **Allowable hole:** Homeomorphisms and constructions of induced topologies
  remain later work.

## Dependency map

```text
native set objects and operations
  -> is_topology_on                       [definition]
  -> TopologicalSpaceSetting              [universal context]
  -> finite open-set laws                 [proof]

two topology facts + open preimages
  -> is_continuous                        [definition]
  -> ContinuousCompositionSetting         [universal context]
  -> continuous composition               [proof]
```

## Intended build order

Define candidate topologies, prove small closure consumers through the named
setting, define continuity by open preimages, then prove composition with one
explicit preimage-equality bridge.

## Interface decisions and permissible gaps

Use settings for ordinary ambient theorems and explicit parameters in
definitions. Introduce a struct only when a later construction needs a
topological space as data. Do not create aliases for native set operations.
