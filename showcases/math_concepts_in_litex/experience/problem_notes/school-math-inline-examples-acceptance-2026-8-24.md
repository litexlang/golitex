# School-math inline examples acceptance

## Tracer

Symmetric difference is representative because it shows the full structural
change: a reusable definition and its concrete caller formerly lived in two
exports, while they now read and verify together in one section of `main.lit`.

```litex
# Before (registered examples submodule):
# main::symmetric_difference({1, 2}, {2, 3}) = union(set_minus({1, 2}, {2, 3}), set_minus({2, 3}, {1, 2}))
# 1 $in main::symmetric_difference({1, 2}, {2, 3})
# Former behavior: the caller lived in examples/sets_and_logic.lit and needed
# the main:: namespace qualifier.

# Now (active in main.lit):
have fn symmetric_difference(A, B power_set(R)) power_set(R) = union(set_minus(A, B), set_minus(B, A))
symmetric_difference({1, 2}, {2, 3}) = union(set_minus({1, 2}, {2, 3}), set_minus({2, 3}, {1, 2}))
1 $in symmetric_difference({1, 2}, {2, 3})

# Boundary: this changes source layout and removes the examples namespace; it
# does not widen the real-valued set interface or change verifier semantics.
```

The active registered source is
`showcases/math_concepts_in_litex/1_middle_school_math_in_nutshell/main.lit`.
The excerpt above is explanatory; the registered source, not this Markdown
block, is what the runner executed.

## Result

- All distinct applications from the former eleven example files appear in
  their matching numbered sections of `main.lit`.
- Exact facts that were already active in `main.lit` remain single copies.
- `litex.config` exports only `main`; the former `examples/` directory and
  namespace are absent.
- No `trust`, `axiom`, or `abstract_prop` was introduced.

## Evidence

- Persistent tracer session:
  `target/release/litex -compact -session -before showcases/math_concepts_in_litex/1_middle_school_math_in_nutshell/main.lit`
  returned a `block` event with `id: tracer-001` and `ok: true` for the opening
  facts, definition, and unqualified membership application.
- Focused file gate:
  `target/release/litex -compact -runner -f showcases/math_concepts_in_litex/1_middle_school_math_in_nutshell/main.lit`
  exited `0` with top-level `result: success` and `ok: true`.
- Complete showcase gate:
  `target/release/litex -compact -runner -r showcases/math_concepts_in_litex/1_middle_school_math_in_nutshell`
  exited `0` with top-level `result: success` and `ok: true`.
