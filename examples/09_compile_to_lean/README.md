# Litex-to-Lean example ledger

[`compile_to_lean_examples.md`](compile_to_lean_examples.md) is the growing,
reader-facing executable feature ledger for the universal-object compiler.
Every new supported capability appends its harness program as one independent
`litex` fence. The file is intentionally expected to become longer over time:
its order records how compiler coverage grew.

The harness checks that generated source:

- imports the shared `Litex.Object` universe and `Litex.In` ABI;
- contains the expected proof route for that section;
- contains no old native-carrier fragments such as `Set ℝ`, native numeric
  binders, widening, downcast, or `LeanCarrier`;
- compiles as a complete file in a real Mathlib Lake project when the ignored
  kernel gate is enabled.

Every Litex program in the ledger is followed by the complete Lean file
actually emitted by the current compiler. The Rust harness compares that
snapshot byte-for-byte with a fresh compilation, and the Mathlib gate compiles
the complete result. The smaller required-shape block remains as a readable
contract, but it cannot stand in for actual generated output. A proposed entry
that does not compile must be marked `TODO` with its current compiler error.

For an ad hoc source-to-target inspection, put one complete Litex program in
`examples/tmp.lit` and run:

```text
cargo test --release tmp0_to_lean -- --nocapture
```

That scratch command prints the complete Litex input and the exact generated
Lean file as one labeled pair. It is intentionally read-only; the chronological
ledger remains the persistent record of supported compiler capabilities.

## Current feature history

| Section | Demonstrates |
| --- | --- |
| `well_defined_object_dag` | Stable verifier-owned object IDs, child-before-parent emission, and reuse of one frozen outer application |
| `trusted_forall_atomic_fact` | `abstract_prop`, one explicit trusted universal axiom, and exact-`FactId` replay for a concrete atomic theorem |
| `proof_carrying_arithmetic` | Exact WD proof slots for `+`, `-`, `*`, and partial `/`, including quotient closure reused by an outer constructor |
| `inferred_forall_premise` | Verifier-inferred local facts emitted in source order and replayed by exact `FactId` inside a `forall` |
| `proof_carrying_list_set` | Ordered list-set child IDs and the complete indexed pairwise-distinct WD matrix consumed by `Litex.listSet` |
| `object_choice` | Noncomputable choice from exact nonemptiness evidence and its membership `FactId` |
| `existential_intro_elim` | Positive existential construction and ordered witness projections |
| `case_and_contradiction_scopes` | Branch-local and contradiction-local `FactId` scopes |
| `named_theorem` | Source theorem naming, ordered nested steps, and complete-forall ownership |
| `total_object_constructors` | Closed `pi` and total binary `union` without proof arguments |
| `proof_carrying_division` | Dedicated two-membership-plus-nonzero partial constructor contract |
| `set_builder_scope` | SymbolId-owned predicate binder with no scope leakage |
| `named_function` | Checked body/range construction, membership, definition, and replay |
| `indexed_aggregate` | One tuple constructor with dimension checks and ordered interface facts |
| `statement_object_interactions` | Witness-as-argument, cases-in-theorem, and set-builder return-set composition |

## Adding a feature entry

Append one lowercase snake-case H2 section; do not rewrite an older feature
entry to make room. Include the focused harness source path, one self-contained
`litex` fence, its complete current generated Lean snapshot, the essential
required shape, the nearest rejected boundary, and the exact focused gates.
Then register the entry's invariant in
`src/compile_to_lean/universal_examples_tests.rs` and update the expected
section count. Add a negative Rust regression when semantics widen. Never fill
an actual-output block by hand from the required shape: generate it, compile
it, and let the byte-for-byte ledger check detect drift.

Candidate harnesses do not enter the executable history early. The ranked
statement-object basis and each candidate's current strict compiler boundary
live in [`math_collections.md`](math_collections.md#statement-object-harness-basis).
Implement them in that evidence-driven order unless a real caller establishes
a stronger dependency.

This ledger was deliberately reset before growing into the feature history above. Earlier
compiler scenarios remain covered by the combined showcase and focused Rust
tests, but they are not copied into this chronological feature history.

## Verification

```text
cargo test --release universal_examples_compile_to_the_new_abi -- --nocapture

LITEX_LEAN_PROJECT=/absolute/path/to/mathlib \
LITEX_LAKE=/absolute/path/to/lake \
cargo test --release universal_examples_compile_with_mathlib -- --ignored --nocapture

target/release/litex -compact -isolated -runner -f \
  examples/05_compiler_interop/compile_to_lean_well_defined_object_dag.lit

target/release/litex -compact -isolated -runner -f \
  examples/05_compiler_interop/compile_to_lean_trusted_forall_instantiation.lit
```

Strict compilation remains fail-closed. Unsupported proof routes never become
`sorry`, compiler-invented axioms, or calls into the deleted native backend.
