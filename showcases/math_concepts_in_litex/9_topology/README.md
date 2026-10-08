# Topology

This settings-first topology showcase has a checked elementary theorem chain. It uses
native `intersect`, `union`, `family_union`, subset, and set-builder preimages;
derives binary-union and three-way-intersection closure; defines continuity by
open preimages; proves the closed-preimage characterization of continuity in
both directions; defines compact subsets by indexed open covers; and proves
that the continuous image of a compact subset is compact.
`TopologicalSpaceSetting` is the single source of the topology parameters and
laws. `TopologicalMapSetting` and `ContinuousMapSetting` compose renamed
topology bundles into the reusable map contexts consumed by the theorems.

This is the topology stopping boundary for the first collection version:
topological setting, continuous maps, the closed-preimage characterization,
indexed compactness, and compact images. Bases, filters, separation axioms,
connectedness, quotient topology, and algebraic topology are optional later
subjects rather than gaps in this module.

`main.lit` contains no `trust`. Both the independent release file runner and
module runner return top-level `success: true`. See `math_collections.md` for the
fixed scope and interface decisions.

`same_math_in_lean.lean` defines sets as predicates, packages
the topology laws as a structure, derives binary-union closure, and proves
continuity under composition using only Lean's automatically loaded Prelude.
It has no imports and is a handwritten formulation of the same mathematics, not compiler-generated
output. Run it with:

```sh
lean showcases/math_concepts_in_litex/9_topology/same_math_in_lean.lean
```

## Current callable interfaces

Preimages, composition and function restriction have named templates. The proofs explicitly release their membership, carrier and value lemmas; restrictions retain the exact source subset and original map. Indexed compactness still asks for a finite subcover, and the compact-image theorem proves that conclusion without extra assumptions.

The set-builder template is named `inverse_image`, and its powerset lemma is `preimage_powerset`. The names `preimage` and `preimage_set` belong to the new builtin object constructors.
