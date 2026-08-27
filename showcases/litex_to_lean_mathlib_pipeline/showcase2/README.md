# Real Cauchy sequences: Litex → Lean → Mathlib

This showcase gives one end-to-end, axiom-free example of real sequential
completeness:

1. `main.lit` defines convergence of a real sequence.
2. `main.lit` defines the Cauchy property.
3. `main.lit` proves `cauchy_sequence_converges` as a `thm`.
4. the compiler alone writes `LitexGenerate.lean`;
5. `LitexToMathlib.lean` exposes the generated theorem to ordinary Mathlib
   sequence vocabulary.

## Ownership

| File | Owner | Role |
| --- | --- | --- |
| `main.lit` | author | Litex definitions and theorem |
| `LitexGenerate.lean` | Litex compiler | exact generated Lean; never hand-edit |
| `LitexToMathlib.lean` | adapter author | Mathlib-facing bridge and downstream examples |
| `litex.config` | module | local Litex entry point |

The source contains no `axiom` and no `trust`. The verifier's reserved,
real-only completeness certificate accepts only the five epsilon definitions
in this file. Its generated proof calls
`Litex.Rules.realCauchySequenceConverges`, which is proved from Mathlib's
`CompleteSpace ℝ`; there is no project axiom, `sorry`, or `admit` in the path.

Litex sequences use positive-natural indices. The Lean rule views the same
sequence as a Mathlib sequence on `ℕ` by sending `n` to the Litex index
`n + 1`. A positive Litex cutoff is correspondingly translated to a
zero-based cutoff by subtracting one.

## Reproduce

Run from the repository root:

```bash
cargo build --release
target/release/litex -compact -strict -runner -isolated \
  -f showcases/litex_to_lean_mathlib_pipeline/showcase2/main.lit
target/release/stmt_result_to_lean_compiler compile \
  showcases/litex_to_lean_mathlib_pipeline/showcase2/main.lit \
  showcases/litex_to_lean_mathlib_pipeline/showcase2/LitexGenerate.lean
cd lean
lake build LitexGenerate LitexToMathlib
```

Regenerating `LitexGenerate.lean` must produce no diff.
