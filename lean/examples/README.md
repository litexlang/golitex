# Litex-to-Lean example ledger

[`compile_to_lean_examples.lit`](compile_to_lean_examples.lit) is the executable
source ledger for the universal-object compiler. Each mathematical example is
introduced by a short comment and isolated in its own `sketch`. Run:

```text
litex -lean \
  lean/examples/compile_to_lean_examples.lit \
  lean/examples/compile_to_lean_examples.lean
```

This directory lives inside the canonical [`lean/`](../) Lake project, beside
the shared `Litex` target ABI. The Lean extension therefore uses the matching
toolchain and resolves `import Litex.Rules` without a second project or a copy
of the ABI. Check the generated file from `lean/` with:

```bash
lake env lean examples/compile_to_lean_examples.lean
```

On a fresh checkout, run `lake build` in `lean/` once before opening or
checking the generated file.

The checked-in [`compile_to_lean_examples.lean`](compile_to_lean_examples.lean)
is the exact generated result and compiles as one complete file in the bundled
Mathlib Lake project. The generated source:

- imports the shared `Litex.Object` universe and `Litex.In` ABI;
- contains the expected proof route for that section;
- contains no old native-carrier fragments such as `Set ℝ`, native numeric
  binders, widening, downcast, or `LeanCarrier`;
- compiles as a complete file in a real Mathlib Lake project.

[`compile_to_lean_examples.md`](compile_to_lean_examples.md) remains the
reader-facing detailed feature history. Each section shows the standalone
Litex case, its complete generated Lean snapshot, the essential target shape,
and the nearest rejected boundary.

Every Litex program in the ledger is followed by the complete Lean file
actually emitted by the current compiler. The smaller required-shape block is a
compact description of the essential mapping and does not replace the complete
output. Ordinary function types appear as `fnSpace1` through `fnSpace5`, or as
generic `fnSpace` for larger arities; dependent function types retain the
advanced `FnSpec` layer. Compiler-owned Lean names use the reserved `__`
prefix. `cases/` contains the corresponding standalone Litex sources.

## Current feature history

| Section | Demonstrates |
| --- | --- |
| `well_defined_object_dag` | Readable `fnSpace1`/`fnSpace2` types, reserved `__` helper names, stable verifier-owned object IDs, and child-before-parent WD replay inside the owning theorem scope |
| `trusted_forall_atomic_fact` | `abstract_prop`, one explicit trusted universal axiom, and exact-`FactId` replay for a concrete atomic theorem |
| `proof_carrying_arithmetic` | Proof-free `+`, `-`, `*`, `/` terms plus exact local operand slots and a theorem-local intrinsic result proof, including quotient closure reused by an outer operation |
| `inferred_forall_premise` | Verifier-inferred local facts emitted in source order and replayed by exact `FactId` inside a `forall` |
| `proof_carrying_list_set` | Proof-free list-set terms plus ordered child IDs and the complete local indexed pairwise-distinct WD matrix |
| `object_choice` | Noncomputable choice from exact nonemptiness evidence and its membership `FactId` |
| `existential_intro_elim` | Positive existential construction and ordered witness projections |
| `case_and_contradiction_scopes` | Recursive branch-local statements and WD, exact conjunct projections, contradiction-local `FactId`s, and negative-goal double-negation replay |
| `example_and_sketch` | Anonymous checked goals lowered to Lean `example`; targetless checked blocks replayed in isolated Lean namespaces without exporting Litex facts |
| `named_theorem` | Source theorem naming, ordered nested steps, and complete-forall ownership |
| `total_object_constructors` | Closed `pi` and total binary `union` without proof arguments |
| `proof_carrying_division` | Proof-free division denotation with a dedicated two-membership-plus-nonzero WD certificate |
| `set_builder_scope` | SymbolId-owned predicate binder with no scope leakage |
| `owned_construction_scopes` | Ordered set-builder condition WD and compound anonymous-function body replay under their exact owner binders |
| `named_function` | Dependent requirements telescope, proof-free `inc`/`reciprocal` bodies, local closure evidence, membership, definition, and exact replay |
| `indexed_aggregate` | One tuple constructor with dimension checks and ordered interface facts |
| `aggregate_objects` | Big union/intersection, power set, general Cartesian products, integer ranges, indexed and finite-set folds, tuple/sequence literals, and sequence carriers as proof-free object terms with binder-local WD replay |
| `statement_object_interactions` | Witness-as-argument, cases-in-theorem, and set-builder return-set composition |
| `anonymous_function` | Alpha-equivalent anonymous functions, checked return membership, and separate application evidence |
| `arithmetic_forall_wd` | Nested universal facts, subtraction closure, and occurrence-owned application evidence |
| `first_statement_tranche` | Abstract and defined predicates, object definitions, definition folding, and explicit trust |
| `known_equality_path` | Equality symmetry and transitivity replayed from exact stored facts |
| `litex_object_abi` | One target object type with independent numeric and function-domain memberships |
| `set_predicate_definitions` | Nonempty and finite set predicates derived from the shared membership model |
| `shared_builtin_rules` | Generated proofs calling checked theorems from `Litex.Rules` |

Strict compilation remains fail-closed. Unsupported proof routes never become
`sorry`, compiler-invented axioms, or calls into the deleted native backend.
