# Mathematical Collections: Topology

## Purpose and scope

This standalone version models topologies as collections of open sets and
proves a short theorem chain through named settings. It targets readers who
know elementary sets and functions. It reaches closed sets, the closed-set
criterion for continuity, indexed-cover compactness, and preservation of
compactness by continuous images. Bases, filters, connectedness, separation,
and quotient constructions remain outside this checkpoint.

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
- **Ideal Litex form:** `prop is_topology_on(X, open_sets)`.
- **Interface sketch:** `open_sets power_set(power_set(X))` with the standard
  axioms.
- **Nearest wrong alternative:** A new topology object or custom union
  construction would duplicate native set objects and operations.
- **Dependencies:** Power sets, intersection, `big_union`, and subset.
- **Downstream uses:** `TopologicalSpaceSetting` and open-set closure laws.
- **Allowable hole:** None in the first checkpoint.

### Topological theorem setting

- **Ordinary meaning:** reason in an arbitrary supplied topological space.
- **Semantic role:** Reusable universal theorem context.
- **Ideal Litex form:** `setting TopologicalSpaceSetting(X, open_sets)` as the single
  source of parameters and laws, with `prop is_topology_on([TopologicalSpaceSetting])`
  as the definition-facing interface.
- **Interface sketch:** `forall [TopologicalSpaceSetting], A, B open_sets: ...`
  and `[TopologicalSpaceSetting(Y, open_sets_Y)]` when a second renamed space
  is needed.
- **Nearest wrong alternative:** A struct forces field projection even when
  no theorem passes a topological space as a value.
- **Dependencies:** Candidate topology.
- **Downstream uses:** Binary open unions and three-way open intersections.
- **Allowable hole:** Settings cannot define or return a topology; they only
  contribute parameters and ambient facts.

### Continuity

- **Ordinary meaning:** every open set in the codomain has open preimage.
- **Semantic role:** Relation on two candidate topologies and a function.
- **Ideal Litex form:** `TopologicalMapSetting` composes two renamed topology
  bundles and a function; `ContinuousMapSetting` adds the open-preimage law;
  `prop is_continuous([ContinuousMapSetting])` exposes the ordinary flat ABI.
- **Interface sketch:**
  `prop is_continuous([TopologicalSpaceSetting(X, open_sets_X)], [TopologicalSpaceSetting(Y, open_sets_Y)], f ...)`
  followed only by the open-preimage law.
- **Nearest wrong alternative:** A continuous-map struct is premature before
  callers pass or project packaged maps.
- **Dependencies:** Candidate topologies, functions, and set builders.
- **Downstream uses:** Composition, closed-preimage characterization, and
  preservation of compactness.
- **Allowable hole:** Homeomorphisms and constructions of induced topologies
  remain later work.

### Closed sets and the continuity criterion

- **Ordinary meaning:** `F` is closed when its relative complement is open;
  a map is continuous exactly when every closed set has closed preimage.
- **Semantic role:** Definition plus two directional named theorems.
- **Ideal Litex form:** `is_closed([TopologicalSpaceSetting], F)` and
  `has_closed_preimages([TopologicalMapSetting])`.
- **Interface sketch:** `continuous_map_has_closed_preimages` and
  `closed_preimages_imply_continuous` sit next to one another as the checked
  iff characterization.
- **Boundary:** Litex currently rejects `forall ... <=>:` as a named theorem
  target, so the two theorem directions are intentionally not hidden behind
  an uncheckable wrapper.

### Compact subsets

- **Ordinary meaning:** every open cover has a finite subcover.
- **Semantic role:** Relation on a subset of a topological carrier.
- **Ideal Litex form:** an indexed cover `cover: Index -> open_sets`, with a
  finite `J subset Index` whose restricted range still covers the subset.
- **Nearest wrong alternative:** quantifying over an unindexed family and then
  choosing original cover members from pulled-back sets adds an unnecessary
  choice step.
- **Downstream use:** `continuous_image_of_compact_is_compact`.

## Dependency map

```text
native set objects and operations
  -> TopologicalSpaceSetting              [parameters + topology laws]
  -> is_topology_on                       [bundle-derived definition]
  -> finite open-set laws                 [proof]

two TopologicalSpaceSetting bundles + a function
  -> TopologicalMapSetting                [composed context]
  -> ContinuousMapSetting                 [open-preimage law]
  -> is_continuous                        [bundle-derived definition]
  -> closed-preimage characterization     [two proofs]
three TopologicalSpaceSetting bundles + two open-preimage laws
  -> ContinuousCompositionSetting         [composed universal context]
  -> continuous composition               [proof]
TopologicalSpaceSetting + indexed covers
  -> is_compact_subset                    [definition]
ContinuousMapSetting + compact source
  -> continuous compact image             [proof]
```

## Intended build order

Define candidate topologies, prove small closure consumers, compose the map
settings, prove composition and the closed-set criterion, then define indexed
compactness and pull an arbitrary target cover back to prove compactness of
the image.

## Interface decisions and permissible gaps

Use settings for ordinary ambient theorems and reuse the same setting bundles
in predicates and larger settings. Introduce a struct only when a later
construction needs a topological space as data. Do not create aliases for
native set operations.
