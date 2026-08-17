# Topology

This settings-first topology showcase has a checked elementary theorem chain. It uses
native `intersect`, `union`, `big_union`, subset, and set-builder preimages;
derives binary-union and three-way-intersection closure; defines continuity by
open preimages; proves the closed-preimage characterization of continuity in
both directions; defines compact subsets by indexed open covers; and proves
that the continuous image of a compact subset is compact.
`TopologicalSpaceSetting` is the single source of the topology parameters and
laws. `TopologicalMapSetting` and `ContinuousMapSetting` compose renamed
topology bundles into the reusable map contexts consumed by the theorems.

`main.lit` contains no `trust`. Both the independent release file runner and
module runner return top-level `ok: true`. See `math_collections.md` for the
fixed scope and interface decisions.

For comparison, `lean_core_analogy.lean` defines sets as predicates, packages
the topology laws as a structure, derives binary-union closure, and proves
continuity under composition using only Lean's automatically loaded Prelude.
It has no imports and is handwritten analogy code, not compiler-generated
output. Run it with:

```sh
lean showcases/math_concepts_in_litex/topology/lean_core_analogy.lean
```
