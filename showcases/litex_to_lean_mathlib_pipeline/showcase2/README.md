# Real Cauchy sequences: Litex → Lean → Mathlib

This showcase keeps the current trust boundary explicit:

1. `main.lit` defines convergence of a real sequence.
2. `main.lit` defines the Cauchy property.
3. `main.lit` derives sequential completeness from the kernel-owned
   least-upper-bound completeness of `R`;
4. `LitexToMathlib.lean` independently proves Cauchy completeness using Mathlib's
   `CompleteSpace ℝ` instance and states it in the generated vocabulary.

## Ownership

| File | Owner | Role |
| --- | --- | --- |
| `main.lit` | author | Litex definitions |
| `LitexGenerate.lean` | Litex compiler | checked-in definition output; never hand-edit |
| `LitexToMathlib.lean` | adapter author | Mathlib-facing bridge and downstream examples |
| `litex.config` | module | local Litex entry point |

The source contains no `axiom` and no `trust`. The kernel knows only the order
completeness of builtin `R`: a nonempty real set with a real upper bound has a
least upper bound. There is no sequence-specific completeness builtin.

The Litex proof forms the set of real numbers that lower-bound some tail of the
Cauchy sequence, obtains its supremum from `real_least_upper_bound_exists`, and
uses the two LUB projection theorems to prove eventual epsilon-closeness to that
supremum. The analogous statement over `Q` is not available because the LUB
step fails there.

The Lean compiler does not yet consume every local proof step in this derived
Litex proof. `LitexGenerate.lean` therefore remains the checked-in output for
the original definition layer, while `LitexToMathlib.lean` independently proves
the native Mathlib counterpart. No generated Lean proof is fabricated.

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
cd lean
lake build LitexGenerate LitexToMathlib
```

Lean regeneration is deferred until the compiler supports the remaining local
defined-predicate proof steps. It fails closed instead of emitting an unchecked
proof.
