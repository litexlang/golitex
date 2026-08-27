# Real Cauchy sequences: Litex → Lean → Mathlib

This showcase keeps the current trust boundary explicit:

1. `main.lit` defines convergence of a real sequence.
2. `main.lit` defines the Cauchy property.
3. the compiler alone writes those definitions to `LitexGenerate.lean`;
4. `LitexToMathlib.lean` proves Cauchy completeness using Mathlib's
   `CompleteSpace ℝ` instance and states it in the generated vocabulary.

## Ownership

| File | Owner | Role |
| --- | --- | --- |
| `main.lit` | author | Litex definitions |
| `LitexGenerate.lean` | Litex compiler | exact generated Lean; never hand-edit |
| `LitexToMathlib.lean` | adapter author | Mathlib-facing bridge and downstream examples |
| `litex.config` | module | local Litex entry point |

The source contains no `axiom` and no `trust`. There is deliberately no
reserved Litex completeness theorem. The current Litex foundation treats `R`
as a builtin carrier but does not construct it and does not prove a least-upper-
bound principle. Consequently, the five epsilon definitions alone cannot prove
that every real Cauchy sequence converges. That assertion is exactly the
missing completeness principle (and it is false with `Q` in place of `R`).

`LitexToMathlib.lean` is therefore a one-way, handwritten boundary: it consumes
the generated definitions and proves their Mathlib counterpart from
`CompleteSpace ℝ`. It does not feed a certificate back into Litex or pretend
that Litex verified the completeness theorem.

Litex sequences use positive-natural indices. The adapter views the same
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

An actual Litex proof of `Cauchy => convergent` requires first adding a
non-circular, axiom-free foundation for completeness of `R` (for example a
construction of the real carrier or an independently proved LUB theorem).
