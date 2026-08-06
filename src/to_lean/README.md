# To-Lean Rational Experiment

This module deliberately keeps the existing public entrypoints while using one
small handoff experiment. Litex first runs normally and produces its existing
per-statement JSON. The To-Lean adapter then reads only the JSON `result`,
`statement`, and `rule` fields; it does not call the verifier. If that JSON says
the equality was checked by `bounded symbolic normalization` (or the existing
rational-simplification label), the adapter reparses only the statement text,
lowers its two rational expressions, and emits Lean. Closed `calculation`
results remain supported for compatibility.

The JSON is intentionally the current human-facing output, not a stable proof
IR or proof certificate. This is a tracer bullet for the desired direction,
with that limitation kept explicit.

## Tracer: current JSON handoff

### Before

`to_lean` parsed the source statement and immediately called
`run_stmt_at_global_env`. After success it selected Lean code from the equality
shape, without requiring the normal Litex JSON to say which route had worked.

### Now

For the central example, normal Litex output contains:

```json
{
  "result": "success",
  "statement": "forall a, b, x R:\n    x != 0\n    =>:\n        (a + b) / x = a / x + b / x",
  "conclusions": [
    {
      "statement": "(a + b) / x = a / x + b / x",
      "why_verified": {
        "type": "builtin rule",
        "rule": "bounded symbolic normalization"
      }
    }
  ]
}
```

`to_lean_from_statement_json` can see only this object. It accepts the exact
rule, extracts and reparses the top-level `statement`, and emits a Lean proof
whose comment records `rational expression simplification`. Replacing the JSON
rule with `same known equality class` makes the adapter reject the same
statement.

### Boundary

This adapter relies on current JSON field names, spacing-independent string
extraction, and English rule labels. It does not validate a general proof tree,
connect nested evidence nodes, or establish that the JSON is authentic. Those
are deliberately deferred instead of being disguised as an IR.

### Evidence

```text
cargo test --release normal_statement_json_drives_the_rational_tracer -- --nocapture
cargo test --release current_json_adapter_rejects_a_different_proof_route -- --nocapture
```

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
conjunctions, and general proof provenance are intentionally outside the
experiment. Only the current JSON rule label for this rational route is
consumed; it is not yet translated into a Lean proof certificate.

### Evidence

```text
target/release/litex -compact -runner -e '<the active tracer above>'
cargo test --release to_lean:: -- --nocapture
```

Implementation: `src/to_lean/current_json.rs`,
`src/to_lean/rational_expression.rs`, and `src/to_lean/to_lean_pipeline.rs`.
