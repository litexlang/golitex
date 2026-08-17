# Topology

This settings-first topology showcase has a checked first checkpoint. It uses
native `intersect`, `union`, `big_union`, subset, and set-builder preimages;
derives binary-union and three-way-intersection closure; defines continuity by
open preimages; and proves that continuous maps are closed under composition.

`main.lit` contains no `trust`. Both the independent release file runner and
module runner return top-level `ok: true`. See `plan.md` and
`math_collections.md` for the fixed scope and interface decisions.
