# Separation and compactness from std

The single-file caller compares discrete and indiscrete spaces, including
empty spaces and a carrier {0,1} inside ambient R. It checks separation and
closed singletons, general finite-subset compactness, finite union and actual
restriction images, a noninjective continuous map and a surjective image.

On the same infinite carrier R, the indiscrete space is compact and fails
Hausdorff separation; the discrete space is not compact. The latter is proved
with its singleton open cover: a finite subcover would make R finite. A
continuous constant map from the compact pair into this noncompact target
still has a compact image; its failure of surjectivity is proved explicitly.

contracts/main.lit independently calls all 19 new theorems and checks the
restriction map's exact type and pointwise equation. readme/main.lit is the
new std README excerpt. Each of 28 negative projects accepts its whole setup
and rejects only the final statement at negative/expected.json's phase.

```bash
python3 examples/topology/separation_compactness/check.py
```

The checker includes strict source/positive contracts, actual archive and
shared-data installed imports with LITEX_STD_PATH absent, and std/WiX payload
and component-reference equality. The original foundations project remains
unchanged and is checked separately for compatibility. This is a focused
source-library gate; no Lean or repository-wide release certification.
