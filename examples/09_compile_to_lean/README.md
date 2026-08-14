# Litex-to-Lean example ledger

[`compile_to_lean_examples.md`](compile_to_lean_examples.md) is the growing,
reader-facing executable feature ledger for the universal-object compiler.
Each section contains one independent Litex program and the complete Lean file
currently emitted for it. The generated source:

- imports the shared `Litex.Object` universe and `Litex.In` ABI;
- contains the expected proof route for that section;
- contains no old native-carrier fragments such as `Set ℝ`, native numeric
  binders, widening, downcast, or `LeanCarrier`;
- compiles as a complete file in a real Mathlib Lake project.

Every Litex program in the ledger is followed by the complete Lean file
actually emitted by the current compiler. The smaller required-shape block is a
compact description of the essential mapping and does not replace the complete
output. `cases/` contains the corresponding standalone Litex sources.

## Current feature history

| Section | Demonstrates |
| --- | --- |
| `well_defined_object_dag` | Stable verifier-owned object IDs and child-before-parent WD replay inside the owning theorem scope |
| `trusted_forall_atomic_fact` | `abstract_prop`, one explicit trusted universal axiom, and exact-`FactId` replay for a concrete atomic theorem |
| `proof_carrying_arithmetic` | Proof-free `+`, `-`, `*`, `/` terms plus exact local operand slots and a theorem-local intrinsic result proof, including quotient closure reused by an outer operation |
| `inferred_forall_premise` | Verifier-inferred local facts emitted in source order and replayed by exact `FactId` inside a `forall` |
| `proof_carrying_list_set` | Proof-free list-set terms plus ordered child IDs and the complete local indexed pairwise-distinct WD matrix |
| `object_choice` | Noncomputable choice from exact nonemptiness evidence and its membership `FactId` |
| `existential_intro_elim` | Positive existential construction and ordered witness projections |
| `case_and_contradiction_scopes` | Branch-local and contradiction-local `FactId` scopes |
| `named_theorem` | Source theorem naming, ordered nested steps, and complete-forall ownership |
| `total_object_constructors` | Closed `pi` and total binary `union` without proof arguments |
| `proof_carrying_division` | Proof-free division denotation with a dedicated two-membership-plus-nonzero WD certificate |
| `set_builder_scope` | SymbolId-owned predicate binder with no scope leakage |
| `named_function` | Dependent requirements telescope, proof-free `inc`/`reciprocal` bodies, local closure evidence, membership, definition, and exact replay |
| `indexed_aggregate` | One tuple constructor with dimension checks and ordered interface facts |
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
