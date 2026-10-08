# Plane Geometry in Litex

This standalone showcase introduces plane geometry through real coordinate
pairs, geometric predicates, and proofs. It contains 41 definitions and
186 theorems covering vectors, distances, lines, triangles, circles, and
related geometric constructions.

The source is Jiachen Shen and Keyao Zhu's
[geo.lit](../../../scripts/LitexGeo-AutoBuild/shenjiachen/新geo和geo_definitions/geo.lit).
The showcase copy preserves its definitions, hypotheses, conclusions, and
proof steps. Its 402 theorem calls use `release thm` in place of `by thm`.
The pinned source snapshot remains historical; the current maintained library supplies this migration.

Run the showcase from the repository root:

```bash
cargo build --release --locked
target/release/litex -strict -f showcases/math_concepts_in_litex/15_coordinate_geometry_case_study/main.lit
target/release/litex -strict -r showcases/math_concepts_in_litex/15_coordinate_geometry_case_study
```

`litex.config` exports the complete `main.lit` file. The source contains no
`trust`, axioms, or external imports. Verification evidence is recorded in
the collection's replacement acceptance note.

On 2026-10-05 the maintainer selected this library to replace the former
coordinate-geometry problem collection. The old problem modules and their
unfinished proofs are outside the current showcase scope.

Verification status (2026-10-05): the complete, byte-identical showcase copy
passed strict file verification (227/227). Both its candidate module and the
actual module at this public directory passed on the same release binary.
See the historical acceptance note (retired).

Current migration (2026-10-06): `main.lit` now uses `p(1)` / `p(2)` and
is copied from the maintained current `showcases/2D_Geometry/geo.lit`.
That library preserves the geometry statements and includes explicit named
coordinate bridges in the proofs. The earlier incomplete draft observation
remains in its dated migration evidence; it does not describe this file.

Litex release checks do not require a Lean analogy file. This library has no
`same_math_in_lean.lean`, and no Lean verification is claimed here.
