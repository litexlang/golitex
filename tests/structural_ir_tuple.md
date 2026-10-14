# Structural arithmetic IR and tuple punctuation acceptance

Verified 2026-10-14. Production owners: `src/display_and_ir/obj.rs` and
`src/parse/object/primary.rs`. No AST, Env or Runtime shape changes.

## Before and now

The baseline release accepted all three statements below, including the false
last equality, and also accepted the direct equality of the two power trees:

```text
(2^3)^2 = 64
2^(3^2) = 512
64 = 512
```

The repaired release accepts the first two and rejects the last. The two IR
keys are `((2 ^ 3) ^ 2)` and `(2 ^ (3 ^ 2))`. Independent declarations of
`a=(2^3)^2` and `b=2^(3^2)` no longer prove `a=b` either.

Arithmetic infix and unary-negative nodes retain explicit parentheses.
Generated negative literals use the same numerical key as parsed unary
negatives: `Number(-2)` and `Neg(Number(2))` both serialize to `(-2)`.
Their use as a power base preserves the sign on reparse. This is numerical
canonicalization, not a claim of byte-for-byte AST injectivity for every Obj.

`()` now fails parsing with guidance to use `tuple()`. `(1)` remains grouping;
`(1,)` is a singleton tuple, and `(1,2,)` allows a trailing comma. Explicit
`tuple()` and `tuple(1)` remain valid. The tuple IR prints `tuple()`, `(1,)`,
and `(1, 2)` for arities zero, one, and two respectively.

## Evidence

- `cargo test --release --all-targets --no-fail-fast`: 1869 passed, zero failed.
  This includes six dedicated `structural_ir_tuple` tests, every pair of
  arithmetic infix operators at both nesting positions, generated negatives,
  false identity/equivalence/closed-numeric conclusions, predicate and order
  matching, forall-equality index controls, and malformed tuple syntax.
- `python3 tests/tooling/run_docs_markdown_files.py`: 921 blocks, zero failed.
- `python3 examples/test_statements/run.py --binary target/release/litex --require-no-gaps`:
  52 statement leaves, 393 checks, zero unexpected failures or recorded gaps.
- Strict direct CLI passes for
  `examples/proof_nodes/equal/by_they_are_the_same/structural_arithmetic_ir.lit`
  and `examples/test_objs/tuple_comma_syntax.lit`.
- All ten migrated examples retain their expected positive/negative outcomes.
  Negative checks inspect process failure and rejected statements, rather
  than treating commented former failures as executable tests.

The full Rust gate includes the registered compiler contracts; it does not
claim an external Lean build, a release packaging gate, or a scan of every
unregistered corpus. Old recorded JSON receipts remain historical evidence.
