# Litex-to-Lean example ledger

[`compile_to_lean_examples.md`](compile_to_lean_examples.md) is the
reader-facing and executable ledger for the replacement universal-object
compiler. Every `litex` fence is compiled independently.

The harness checks that generated source:

- imports the shared `Litex.Object` universe and `Litex.In` ABI;
- contains the expected proof route for that section;
- contains no old native-carrier fragments such as `Set ℝ`, native numeric
  binders, widening, downcast, or `LeanCarrier`;
- compiles as a complete file in a real Mathlib Lake project when the ignored
  kernel gate is enabled.

The ledger intentionally records required generated shapes rather than
copying the shared core and theorem bodies into adjacent snapshots.

## Current sections

| Section | Demonstrates |
| --- | --- |
| `membership_wd` | One object keeps both `C` and `R` memberships; an exact named WD fact justifies `f [a]` |
| `set_parameter` | Standard-domain and set parameters share the `Litex.Object` type while retaining distinct propositions |
| `derived_set_predicates` | Nonempty and finite sethood are definitions over `IsSet` and the `In`-extension, not opaque axioms |
| `known_forall` | Exact theorem `FactId` replay with ordered object, membership, and domain proofs |
| `statement_definitions_and_trust` | `abstract_prop`, bodyful `prop`, explicit-value object `have`, exact `by def`, and an explicit-only trust axiom boundary |
| `builtin_theorem` | Three concrete builtin certificates call imported shared theorems rather than repeated bodies or axioms |
| `known_equality_path` | Known equality replays exact `FactId` edges through `Eq.symm` and `Eq.trans` |
| `exact_application_layers` | One list per source application group and `fnSetResult` between nested groups |
| `arithmetic_forall_wd` | Nested forall, universal subtraction, real-closure replay, and exact source-occurrence WD links |
| `proof_carrying_arithmetic` | Addition, subtraction, and multiplication consume ordered verifier-owned complex-membership proofs |

## Adding an example

Add one lowercase snake-case H2 section and one self-contained `litex` fence.
Then register its exact invariant in
`src/compile_to_lean/universal_examples_tests.rs` and update the expected
section count. Add a negative Rust regression for the nearest rejected
boundary when semantics widen.

Standalone `.lit` files are reserved for durable acceptance artifacts whose
meaning depends on a real path or CLI run. The primary artifacts are
`examples/05_compiler_interop/compile_to_lean_litex_object_abi.lit`,
`examples/05_compiler_interop/compile_to_lean_set_predicate_definitions.lit`,
`examples/05_compiler_interop/compile_to_lean_arithmetic_forall_wd.lit`, and
`examples/05_compiler_interop/compile_to_lean_first_statement_tranche.lit`.

## Verification

```text
cargo test --release universal_examples_compile_to_the_new_abi -- --nocapture

LITEX_LEAN_PROJECT=/absolute/path/to/mathlib \
LITEX_LAKE=/absolute/path/to/lake \
cargo test --release universal_examples_compile_with_mathlib -- --ignored --nocapture

target/release/litex -compact -isolated -runner -f \
  examples/05_compiler_interop/compile_to_lean_litex_object_abi.lit

target/release/litex -compact -isolated -runner -f \
  examples/05_compiler_interop/compile_to_lean_set_predicate_definitions.lit

target/release/litex -compact -isolated -runner -f \
  examples/05_compiler_interop/compile_to_lean_first_statement_tranche.lit
```

Strict compilation remains fail-closed. Unsupported proof routes never become
`sorry`, compiler-invented axioms, or calls into the deleted native backend.
