# Litex to Mathlib Pipeline

This showcase is a small, executable vertical slice. It starts from one piece
of natural mathematics, verifies a readable Litex theorem, compiles the typed
verification evidence into Lean, and ends with a separate Mathlib-facing file
that imports the generated theorem for a downstream result.

```text
┌─ Human or AI: mathematical authoring ───────────────────────────┐
│ natural_mathematics.md                                          │
│        ↓ formalize the statement and readable proof             │
│ main.lit                                                        │
└─────────────────────────────────────────────────────────────────┘
        ↓ submit for verification
┌─ Litex: verification and automatic translation ────────────────┐
│ Litex verifier checks main.lit                                  │
│        ↓ produces                                               │
│ typed proof evidence                                            │
│        ↓ consumed by                                            │
│ Litex-to-Lean compiler                                          │
│        ↓ generates; this file is not handwritten                │
│ LitexToMathlibPipelineGenerated.lean                            │
└─────────────────────────────────────────────────────────────────┘
        ↓
┌─ Lean: generated-proof checking ────────────────────────────────┐
│ Lean kernel checks the generated proof terms                    │
└─────────────────────────────────────────────────────────────────┘
        ↓ accepted theorem available for import
┌─ Human or AI: downstream use ───────────────────────────────────┐
│ write LitexToMathlibPipelineDownstream.lean                     │
│ using the generated theorem and Mathlib definitions             │
└─────────────────────────────────────────────────────────────────┘
        ↓
┌─ Lean: downstream checking ─────────────────────────────────────┐
│ Lean kernel checks closedIntervalNonemptyOfLt                   │
└─────────────────────────────────────────────────────────────────┘
        ↓
reusable ordinary Lean/Mathlib theorem about Set.Icc
```

Human or AI authors choose the mathematics, write the Litex source, and choose
the downstream application. Litex verifies the Litex source and translates
its typed evidence into Lean. Lean independently checks both the generated
proof and the downstream theorem.

The generated file is not a handwritten “same theorem in Lean” comparison.
It is compiler output and is checked into the showcase so the translation can
be inspected, imported, and protected by a drift test.

## What the MVP proves

`main.lit` verifies that `a < b` implies `a <= b` for real numbers. The
compiler preserves its canonical Litex-facing theorem and additionally emits
the native signature

```lean
theorem litex_real_lt_to_le (a b : ℝ) (h : a < b) : a ≤ b
```

under the generated `Native` namespace.
`LitexToMathlibPipelineDownstream.lean` imports that theorem and uses it to
construct a member of `Set.Icc a b`. Passing `lake build` means both the
generated theorem and its downstream use were accepted by the real Lean kernel
in the repository's Mathlib environment.

The native theorem is not obtained by pretending that the canonical
`Litex.In.rep` choice definitionally equals the caller's real value. Both Lean
views are generated from the same typed strict-to-weak order evidence; the
native view replays that rule through the allowlisted real-order bridges.

## Deliberate boundary

This is one closed compiler slice, not a claim of general native export. It
accepts exactly a named theorem with two direct `R` binders, the premise
`a < b`, the conclusion `a <= b`, and matching typed verifier evidence. Other
shapes continue to emit only their canonical Lean view. In particular, native
equality export is outside this MVP because it requires separately reviewed
wrapper elimination.

There is no project axiom, `sorry`, `admit`, or silent fallback in this chain.
