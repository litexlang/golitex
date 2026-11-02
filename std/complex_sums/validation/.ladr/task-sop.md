# LADR polynomial-interface continuation SOP

Status: active. Scope remains A–B std interfaces/proofs plus full FTA and actual
dependencies; the selected target is unfinished. Item 1.8 remains explicitly
deferred under the user-selected std-only boundary. Current catalogue: 58/119.

## Intent and anchors

- Continue from std/complex_sums/main.lit (10 declarations), growth.lit (15)
  and coefficients.lit (9), with source-owned hashes and journals in this folder.
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
- Same-bound and cross-bound coefficient uniqueness and finite zero padding
  pass source/imported/retained-context gates: 9 final source / 64 use / 7 refusals.
  Continue in std/polynomials, preserving Algebra's actual polynomial functions.
- Journal each material attempt, retain normal failures in the same Session, and
  materialize only accepted contiguous source at coherent checkpoints.
- The R/C bridge source gate passes 9 declarations, its imported file passes
  37 statements and its six refusals pass clean retained-context replay. Preserve
  Session 37471's accepted truncation/finite-degree/bounded-space context. The
  degree_value's 21-statement unique-existence specification. Session 79317
  deliberately reloads the registered 9/5/13/6/21 prefix plus ExtendedReal so
  the committed case-defined prototype can be replaced by the unique selector.
  Canonical degree-value gate 94519 passes all 21 statements. Session 79317
  accepts the 33-statement total selector and bounded-space equivalence. The
  saved source and independent 163-statement caller now pass, with ten clean
  retained-context refusals. LADR 2.11/2.12 are accepted. Session 83226 preserves
  the final consumer context after the earlier hard-stop recovery.
  Continue chapter 3 interfaces in std/linear_maps and actual FTA dependencies.
  Continue remaining A–B and FTA work without marking a dependency as full FTA.

## Completion evidence

- Strict source and independent caller gates: exit 0, Normal success, every
  target statement accepted, no errors or session termination, fixed source and
  executable hashes. Negative cases must reject while preserving valid context.
- Update exact source interfaces, domains, reused dependencies, boundaries,
  source-owned receipts and the accepted-item ledger only after matching gates.
- Cargo/release/textbook-wide gates are outside this source-only change; scripts
  and documentation destinations receive no new authored files from this work.

