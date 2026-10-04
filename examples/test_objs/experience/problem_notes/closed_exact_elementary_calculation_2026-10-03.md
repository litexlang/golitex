# Closed exact elementary calculation — 2026-10-03

The user approved proposals 1–4: rational rounding/integer operands, numeric
radicals, complex parts/arithmetic, and exact rational logs. Pure closed values
belong to calculation, with no Runtime/VerifyState/premise callback. Symbolic
identities retain their existing builtin rule/strategy owners. Modular-power
optimization and finite-set extensions were explicitly excluded.

## Tracer and baseline

```litex
# Before: the same assertion rejected with success=false and exit 1.
# floor(-7/3)=-3
floor(-7/3)=-3
eval floor(-7/3)
```

The accepted assertion uses exact Euclidean floor on the normalized fraction;
`eval` displays `-3` and stores no fact. Baseline `sign(1/3-1/2)=-1` and
`1/(1+i)=(1-i)/2` already verified; they are preserved, not counted as newly
unblocked assertions. Their shared numeric display paths were extended.

## Owners and exact boundaries

- `exact_rational` supplies floor/ceil/sign, integral operand checks, perfect
  rational square roots, and rational logs from proportional prime valuations.
  Existing integer domains stay mandatory, including the exclusion of gcd(0,0).
- `exact_complex` supplies rational-coordinate arithmetic, projections and display.
- `exact_radical` owns canonical rational linear combinations of distinct
  square-free positive roots, exact sums/products, integer powers and division
  by a single radical term. Rational linear independence makes equality and
  disequality coefficient comparison exact. No radical order solver or general
  radical field inverse is added.
- Shared factorization proves every factor, stops above trial divisor 10,000
  and declines an unproved residual. Radical decomposition is limited to 64
  levels and 64 terms; fraction coefficients use checked i128 arithmetic.
- Source WD remains before calculation/evaluation. Zero denominators, negative
  square-root arguments, nonpositive/unit log bases and nonpositive log arguments
  reject. Unsupported irrational logs and overflowing calculations decline;
  no floating approximation is used as proof evidence.
- The central calculator retains canonical radical objects in Detailed JSON
  with representation `radical`. Normal retains its existing localized closed
  calculation explanation. No AST shape, central state, search permission or
  compiler contract is changed by this task.

## Durable acceptance files

- [closed_fraction_rounding_calculation](../../../proof_nodes/equal/by_builtin_rule/closed_fraction_rounding_calculation.lit)
- [closed_radical_calculation](../../../proof_nodes/equal/by_builtin_rule/closed_radical_calculation.lit)
- [closed_complex_parts_calculation](../../../proof_nodes/equal/by_builtin_rule/closed_complex_parts_calculation.lit)
- [closed_rational_log_calculation](../../../proof_nodes/equal/by_builtin_rule/closed_rational_log_calculation.lit)

Each file preserves its actual old rejected line as a comment, active supported
code, the negative boundary and its strict CLI command. The four files are also
collected by `run_examples_closed_exact_elementary_tracers`. Seventeen standalone
controls live in [the negative directory](../../../negative/closed_exact_elementary_calculation/).

## Verification

- Final source fingerprint: `9d06cf3da753d16b23f90a55ca93efaeec10cd1a004f4bdb43a93a1b89cb9bc7`.
- Executable SHA256: `2fc1190b302f37524817181f53e1493e6670dea74f661e93f5f89f61bba5f836`.
- Release build and all final gates had stable source fingerprints.
- 29 selected Rust tests passed: 9 feature/artifact tests, 6 closed numeric view
  tests, 13 central entry/evidence tests and 1 eval source-domain test.
- 75 strict CLI checks passed with exit/JSON agreement: four complete tracers,
  17 negative fixtures, 33 new positive and six new negative Obj cases,
  13 complete owning Obj files (119 positive cases), and two executable docs blocks.
- Coverage audits retain 99 Obj leaves and 99 owning files; nine runner protocol
  tests passed. New fixtures contain no trust.
- Final live manifest: 627 positives, 295 negatives, 22 unrelated recorded gaps.
  This scoped gate is not a new whole-corpus or Lean certificate.

The initial Cargo test compile was blocked by an independently added module
whose test file had not yet appeared. That file was subsequently supplied and
all final Cargo gates passed. Intermediate output tests caught existing renderer
spacing (`sqrt (3)`) and Chinese Normal localization (`封闭计算`); only test
expectations were corrected. The journal preserves failed attempts, the persistent
session, accepted/failed JSON envelopes, full commands and build identities.

[Structured final report](../../closed_exact_elementary_calculation_results_2026-10-03.json)
and [complete journal](../../proof_journals/closed_exact_elementary_calculation_2026-10-03.json).

## Standard release entry after concurrent changes

`cargo build --release` refreshed `target/release/litex`; that executable passes
all four positive tracers and seventeen executable negative controls. Independent
builtin, WD and output edits continued during both default builds, so their source
fingerprints changed. These additional executions are retained separately in the
journal and are not treated as exact current-source certificates. The stable
29-Rust/75-CLI snapshot above is the scoped acceptance record; this task's numeric
producers and calculator/eval consumers remained unchanged at handoff.
