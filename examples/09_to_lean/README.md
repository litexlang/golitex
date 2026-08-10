# Litex-to-Lean Runnable Repository

This configured example repository is a reader-facing inventory of the
currently checked Litex-to-Lean slice. Every `.lit` file verifies in Litex.
All files except `carrier_boundaries.lit` and `partial_boundary.lit` also
compile independently through the strict To-Lean pipeline without `sorry` or
compiler-invented axioms.

Explicit Litex `trust` appears only in `propositions_and_trust.lit`; those
statements deliberately become visible Lean axioms. All other strict examples
produce definitions and theorems without a trust boundary.

## Examples

| File | Demonstrates |
| --- | --- |
| `native_carriers.lit` | Primary tracer: bare equality and `2 $in R` on native `ℝ` |
| `bounded_facts.lit` | Bounded `forall`, retained membership premises, rational normalization |
| `propositions_and_trust.lit` | `abstract_prop`, defined `prop`, known-forall use, explicit trust provenance |
| `object_definitions.lit` | A checked real `have x R = value` definition and its generated facts |
| `equality_transport.lit` | Unary/binary predicate transport and resolved arithmetic arguments |
| `builtin_arithmetic.lit` | Twenty typed arithmetic and order builtin rules |
| `recursive_arithmetic.lit` | A recursively structured positive-addition proof tree |
| `native_sets.lit` | Polymorphic `Set α`, union, intersection, and set difference |
| `choice.lit` | Checked choice from a nonempty native carrier, globally and locally |
| `existentials.lit` | Existential introduction, extraction, projections, and multiple witnesses |
| `proof_scopes.lit` | Object definitions, `by cases`, and `by contra` proof scopes |
| `carrier_boundaries.lit` | Litex-verified carrier facts whose proof routes are not all in the strict backend |
| `partial_boundary.lit` | Honest partial compilation around one unsupported trigonometric proof |

Each strict source file is self-contained for To-Lean compilation. The
configured module also runs all files in the export order above.

Every `.lit` file ends with its corresponding generated Lean source inside a
triple-quoted Litex comment. Strict files contain the complete strict output;
the two boundary files contain exactly the Lean retained by report mode.

## Run The Repository

Build the release binary once:

```text
cargo build --release
```

Verify the complete Litex repository:

```text
target/release/litex -compact -runner -r examples/09_to_lean
```

Generate checked Lean for every strict file and validate the partial report:

```text
cargo test --release to_lean_examples_repository_emits_checked_source -- --nocapture
```

Refresh all trailing Lean snapshots after an intentional compiler change:

```text
cargo test --release refresh_to_lean_examples_repository_snapshots -- --ignored --nocapture
```

The ordinary checked-source test above also compares every snapshot byte for
byte with current compiler output, so stale comments fail the test.

Compile every generated result against an existing Mathlib Lake project:

```text
LITEX_LEAN_PROJECT=/path/to/mathlib4 \
LITEX_LAKE=/path/to/lake \
cargo test --release generated_to_lean_examples_repository_compiles_with_mathlib -- --ignored --nocapture
```

The ignored test invokes `lake env lean` on all 13 generated results. Set
`LITEX_LAKE` only when `lake` is not available on `PATH`.

The strict pipeline is fail-closed. Unsupported proof routes do not silently
become `sorry`, opaque declarations, or axioms. Both boundary files use the
report API instead: it emits independently checked statements, identifies
unsupported statements, and marks the result incomplete.

The commented real-division definition in `object_definitions.lit` records a
separate real-kernel boundary: the emitted declaration must become
`noncomputable` before that source line belongs in the strict runnable set.
