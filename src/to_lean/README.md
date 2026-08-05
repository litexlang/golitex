# To-Lean Rational Experiment

This module deliberately keeps the existing public entrypoints while replacing
the former broad emitter with one small experiment: verified equalities over
`R` are lowered recursively to rational-expression pairs and discharged in Lean
with `norm_num` for closed numeric facts, `ring` for polynomial facts, or
`field_simp` followed by `ring` when a symbolic denominator remains.

## Tracer: chained numeric division

### Before

```litex
# 1 / 2 / 3 / 4 = 1 / 24
```

The recursive lowering already accepted this shape, but it had no dedicated
regression and selected a generic `field_simp` fallback whose unused branches
produced Lean linter warnings for a closed numeric fact.

### Now

```litex
1 / 2 / 3 / 4 = 1 / 24
```

Litex parses `/` left-associatively, so the left side is
`(((1 / 2) / 3) / 4)`. The recursive lowering walks that actual object tree and
produces the structural pair:

```text
numerator   = 1
denominator = (2 * 3) * 4
```

The right side produces `(1, 24)`. The generated Lean `calc` compares the two
fractions with `norm_num`; it compiles without `sorry` and without warnings.

### Boundary

This tracer locks nested division, not Rust-side canonical reduction: the
translator deliberately retains `(2 * 3) * 4` rather than printing `24` itself.

### Evidence

```text
target/release/litex -compact -runner -e '1 / 2 / 3 / 4 = 1 / 24'
cargo test --release chained_numeric_division_reaches_the_recursive_fraction_pipeline -- --nocapture
```

## Tracer: recursive rational equality

### Before

Before, the general-purpose emitter recursively translated many unrelated Litex
statement and object forms and selected a broad tactic mixture. The source below
did not expose or use its recursively constructed fraction pair:

```litex
# forall a, b, x R:
#     x != 0
#     =>:
#         (a + b) / x = a / x + b / x
```

Former behavior: the generated proof jumped directly to
`field_simp [*] <;> ring <;> nlinarith` as one generic tactic choice.

### Now

```litex
forall a, b, x R:
    x != 0
    =>:
        (a + b) / x = a / x + b / x
```

The same verified fact is now the central supported case. The recursive lowering
records `(numerator, denominator)` for each side and uses both pairs in a
three-link Lean `calc` from the original left expression to the original right
expression. Each link is checked with:

```lean
by
  solve
    | field_simp [h1]
    | field_simp [h1] <;> ring
```

### Boundary

This is not a general Litex-to-Lean compiler. It accepts only closed direct
equalities and universal equalities with `R` parameters, plus explicit `!=`
premises when symbolic denominators need them. Transcendental functions,
definitions, claims, theorem bodies,
conjunctions, and proof provenance are intentionally outside the experiment.
The existence of a Litex verification result is not yet translated into a Lean
proof certificate.

### Evidence

```text
target/release/litex -compact -runner -e '<the active tracer above>'
cargo test --release to_lean:: -- --nocapture
```

Implementation: `src/to_lean/rational_expression.rs` and
`src/to_lean/to_lean_pipeline.rs`.
