# Geometry Foundation Import Fixture

This small module supports the qualified-import arithmetic regression in
`examples/01_proof_patterns/import_alias_qualified_arithmetic.lit`.

It exports two checked real constants:

- `main::a`, with value `1`;
- `main2::b`, with value `2`.

Run the public tracer from the repository root with:

```text
target/release/litex -compact -isolated -runner -f examples/01_proof_patterns/import_alias_qualified_arithmetic.lit
```

The module contains no trust, axiom, or abstract proposition boundary.
