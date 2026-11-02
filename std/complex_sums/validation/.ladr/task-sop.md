# LADR polynomial-interface continuation SOP

Status: active. Scope remains A–B std interfaces/proofs plus full FTA and actual
dependencies; the selected target is unfinished. Item 1.8 remains explicitly
deferred under the user-selected std-only boundary. Current catalogue: 53/119.

## Intent and anchors

- Continue from std/complex_sums/main.lit (10 declarations) and growth.lit
  (14 declarations), with source-owned gate hashes and journals in this folder.
- Retain native polynomial functions and exact coefficient domains, including
  zero degree and trailing zeros. Use positive-real restrictions explicitly;
  never identify functions with different complete input domains.
- Authored implementation and verification artifacts stay under std/. Existing
  experiments/std-library-development plans/progress remain separately authorized.
  No kernel, parser, AST, Env/Runtime, compiler, trust or axiom changes.

## Action protocol

- Preserve the pinned acbc6e6d9bdb9188bf2fb57bdbac22b8981486df925a53cf1154ab2c80d6de2e
  executable. Prior Session handles were confirmed missing after resumption;
  deliberately restore the accepted growth prefix in a new persistent Session.
- Finish same-bound coefficient uniqueness using zero coefficients of a zero
  power representation; then prove finite zero padding and cross-bound uniqueness.
- Journal each material attempt, retain normal failures in the same Session, and
  materialize only accepted contiguous source at coherent checkpoints.
- Run independent uses and necessary refusal controls for growth/uniqueness;
  bridge results to the existing R/C polynomial APIs before degree interfaces.
  Continue remaining A–B and FTA work without marking a dependency as full FTA.

## Completion evidence

- Strict source and independent caller gates: exit 0, Normal success, every
  target statement accepted, no errors or session termination, fixed source and
  executable hashes. Negative cases must reject while preserving valid context.
- Update exact source interfaces, domains, reused dependencies, boundaries,
  source-owned receipts and the accepted-item ledger only after matching gates.
- Cargo/release/textbook-wide gates are outside this source-only change; scripts
  and documentation destinations receive no new authored files from this work.

