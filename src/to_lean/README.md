# To-Lean Rational Experiment

This module deliberately keeps the existing public entrypoints while replacing
the former broad emitter with one small experiment: verified equalities over
`R` are lowered recursively to rational-expression pairs and discharged in Lean
with `ring`, or with `field_simp` followed by `ring` when a denominator remains.

## Tracer

Before, the general-purpose emitter recursively translated many unrelated Litex
statement and object forms and selected a broad tactic mixture:

```litex
# forall a, b, x R:
#     x != 0
#     =>:
#         (a + b) / x = a / x + b / x
```

Now the same verified fact is the central supported case. The recursive lowering
records `(numerator, denominator)` for each side and uses both pairs in a
three-link Lean `calc` from the original left expression to the original right
expression. Each link is checked with:

```lean
by
  field_simp [h1] <;> ring
```

Boundary: this is not a general Litex-to-Lean compiler. It accepts only direct
equalities and universal equalities with `R` parameters and explicit `!=`
premises. Transcendental functions, definitions, claims, theorem bodies,
conjunctions, and proof provenance are intentionally outside the experiment.
The existence of a Litex verification result is not yet translated into a Lean
proof certificate.

Focused evidence:

```text
cargo test --release to_lean:: -- --nocapture
```

Implementation: `src/to_lean/rational_expression.rs` and
`src/to_lean/to_lean_pipeline.rs`.
