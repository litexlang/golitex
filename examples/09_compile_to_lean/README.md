# Litex-to-Lean Example Ledger

[`compile_to_lean_examples.md`](compile_to_lean_examples.md) is the default
reader-facing and machine-checked home for small, self-contained Litex-to-Lean
examples. Adding a compiler example means appending one H2 section with one
`litex` input fence and its complete generated `lean` fence. It does not mean
creating another `.lit` file.

The harness verifies every Litex block in isolation, runs strict Litex-to-Lean or
explicit partial report mode, and compares the adjacent Lean fence byte for
byte with current compiler output. Explicit Litex `trust` appears only in the
`propositions_and_trust` section; those statements deliberately become
visible Lean axioms.

Standalone `.lit` files remain appropriate for module imports, registered
project order, CLI/file-path behavior, or durable acceptance artifacts whose
meaning depends on a real file. None of the current ledger examples needs
those semantics.

## Ledger format

Use a lowercase snake-case H2 identifier. Strict compilation is the default:

````markdown
## example_name

```litex
<self-contained Litex source>
```

```lean
<complete generated Lean source>
```
````

For an intentionally incomplete report-mode example, put
`<!-- to-lean: partial -->` between the heading and Litex fence. Do not use
that marker to hide a strict compiler regression.

## Current examples

| Section | Demonstrates |
| --- | --- |
| `native_carriers` | Primary tracer: bare equality and `2 $in R` on native `ℝ` |
| `coprime_natural_builtin` | Native `$coprime` on `N x N` lowered to Mathlib `Nat.Coprime` with checked reflection |
| `mixed_projected_forall` | Mixed real/set binders whose independently covered conclusions retain separate stored FactIds |
| `bounded_facts` | Bounded `forall`, retained membership premises, rational normalization |
| `propositions_and_trust` | Proposition interfaces, known-forall use, explicit trust provenance |
| `object_definitions` | A checked real `have x R = value` definition and generated facts |
| `equality_transport` | Unary/binary predicate transport and resolved arithmetic arguments |
| `builtin_arithmetic` | Twenty registered arithmetic/order rules with paired Mathlib adapters |
| `recursive_arithmetic` | A recursively structured positive-addition proof tree |
| `native_sets` | Polymorphic `Set α`, union, intersection, and set difference |
| `native_set_builtins` | Checked paired adapters for set equalities, membership, predicates, absolute value, and min/max |
| `standard_numeric_subsets` | Native predicates plus one checked membership projection across the standard numeric-set hierarchy |
| `builtin_predicates` | Native prime/coprime, superset, proper-relation, and negated-comparison propositions with checked reflection and duality routes |
| `choice` | Checked choice from a nonempty native carrier, globally and locally |
| `existentials` | Existential introduction, extraction, projections, and multiple witnesses |
| `obtain_from_existential_prop_definition` | Checked unfolding of one verified concrete prop into the exact existential eliminated by `obtain` |
| `proof_scopes` | Object definitions, `by cases`, and `by contra` proof scopes |
| `function_sets_and_well_definedness` | Native dependent function sets over numeric or user-defined sets, multiple memberships without retyping, checked body/application WD certificates, and exact named-function evaluation |
| `environment_well_definedness_cache` | Environment-owned WD proof IDs/DAGs, exact function-contract cache keys, and one reused Lean helper across statements |
| `carrier_boundaries` | Partial report for carrier facts without complete strict backends |
| `partial_boundary` | Partial report around one unsupported trigonometric proof |

## Verification

Check every pair and fail on a stale Lean fence:

```text
cargo test --release compile_to_lean_examples_markdown_emits_checked_source -- --nocapture
```

Refresh all Lean fences after an intentional compiler-output change:

```text
cargo test --release refresh_compile_to_lean_examples_markdown_snapshots -- --ignored --nocapture
```

Run the general examples harness, which also executes every Litex fence in
this ledger:

```text
cargo test --release run_examples -- --nocapture
```

Compile every generated result against an existing Mathlib Lake project:

```text
LITEX_LEAN_PROJECT=/path/to/mathlib4 \
LITEX_LAKE=/path/to/lake \
cargo test --release compile_to_lean_examples_markdown_compiles_with_mathlib -- --ignored --nocapture
```

The strict pipeline remains fail-closed. Unsupported proof routes never
silently become `sorry`, opaque declarations, or compiler-invented axioms.
The two partial sections emit only independently checked statements and mark
their reports `Incomplete`.
