# StmtResult-to-Lean Coverage Summary

Generated deterministically from current source by `build_inventory.py`.
A source/compiler reference is not a real Lean kernel acceptance result.

Total rows: **1462**

Source fingerprint (SHA-256): `a4f2f9e287527b4d90396e58010069d75003c2572223d7aea25e2008927605d5`

## Rows by axis

| Axis | Rows |
| --- | ---: |
| `atomic_fact` | 30 |
| `builtin_typed` | 199 |
| `builtin_uncatalogued` | 422 |
| `fact` | 8 |
| `fact_proof` | 11 |
| `inference` | 24 |
| `object` | 492 |
| `object_atom` | 3 |
| `statement` | 63 |
| `statement_result` | 63 |
| `tracer` | 69 |
| `well_definedness_result` | 78 |

## Rows by status

| Status | Rows |
| --- | ---: |
| `abi_decision` | 58 |
| `compiler_gap` | 68 |
| `dead_or_duplicate_candidate` | 16 |
| `evidence_gap` | 399 |
| `mapped_not_kernel_checked` | 920 |
| `unreachable` | 1 |

## Rows by owner

- Codex implementation/evidence rows: **1404**
- User semantic-decision rows: **58**

Repeated role rows are collapsed into the seven questions in the Day 1 user decision packet.

## Tracer obligations

- Existing source tracers: **69**
- Required per-route tracers: **1376**
- Not applicable until reachability/dead-code resolution: **17**

A `required` string is an explicit obligation, not a claim that the tracer already exists.

## Status by axis

| Axis | `abi_decision` | `compiler_gap` | `dead_or_duplicate_candidate` | `evidence_gap` | `mapped_not_kernel_checked` | `unreachable` |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `atomic_fact` | 0 | 3 | 0 | 0 | 27 | 0 |
| `builtin_typed` | 2 | 1 | 0 | 3 | 193 | 0 |
| `builtin_uncatalogued` | 8 | 0 | 16 | 395 | 2 | 1 |
| `fact` | 0 | 0 | 0 | 0 | 8 | 0 |
| `fact_proof` | 0 | 1 | 0 | 1 | 9 | 0 |
| `inference` | 0 | 0 | 0 | 0 | 24 | 0 |
| `object` | 48 | 48 | 0 | 0 | 396 | 0 |
| `object_atom` | 0 | 1 | 0 | 0 | 2 | 0 |
| `statement` | 0 | 0 | 0 | 0 | 63 | 0 |
| `statement_result` | 0 | 0 | 0 | 0 | 63 | 0 |
| `tracer` | 0 | 0 | 0 | 0 | 69 | 0 |
| `well_definedness_result` | 0 | 14 | 0 | 0 | 64 | 0 |

## Lean adapter surface

- Compiler-emitted literal `Litex.*` symbols: **246**
- Interpolated Lean symbol templates: **8**
- Interpolated compiler call sites: **46**
- Dynamic sites with a function-local certificate match: **18**
- Dynamic sites selected by an enclosing caller/helper route: **28**
- Builtin IDs with a function-local Lean candidate: **143**
- Mapped builtin IDs requiring callee tracing: **52**

See `lean_adapter_symbols.tsv` and `LeanAdapterSymbols.lean` for the
literal declaration gate. See `dynamic_lean_adapter_sites.tsv` for
templates that require Result-driven generated-module tracers.

### Builtin implementation route kinds

| Route kind | Stable IDs |
| --- | ---: |
| `blocked_evidence_contract` | 26 |
| `blocked_target_abi` | 10 |
| `fixed_reflection_adapter` | 22 |
| `leaf_theorem_adapter` | 127 |
| `missing_typed_certificate_route` | 1 |
| `recursive_result_composition` | 28 |
| `selected_semantic_child` | 86 |
| `shared_adapter_candidate` | 128 |
| `typed_certificate_route` | 193 |

## Builtin identity reconciliation

- Stable rule IDs in source: **621**
- Typed/catalogued IDs: **199**
- Uncatalogued IDs: **422**
- Uncatalogued IDs with a direct production reference: **405**
- Uncatalogued IDs without a direct production reference: **17**
- User-owned ABI decisions: **10**
- Codex-owned implementation/evidence rows: **611**

## Statement/result parity

| Source/result pair | Matched variants |
| --- | ---: |
| `Stmt->SuccessStmtResult` | 8 |
| `UnsafeStmt->SuccessUnsafeStmtResult` | 2 |
| `DefinitionStmt->SuccessDefinitionStmtResult` | 26 |
| `ByStmt->SuccessByStmtResult` | 19 |
| `WitnessStmt->SuccessWitnessStmtResult` | 3 |
| `ProofBlockStmt->SuccessProofBlockStmtResult` | 4 |
| `CommandStmt->SuccessCommandStmtResult` | 1 |

## Checked example trust boundaries

- Registered pairs: **69**
- Trust-free positive pairs: **63**
- Explicit source-declared trust/axiom pairs: **6**
- Checked Lean axioms without a source boundary: **0**

See `example_trust_boundaries.tsv` for exact source and Lean line references.

## Used and unused uncatalogued builtin mechanisms

| Mechanism | Rows |
| --- | ---: |
| `checked_computation_or_reflection` | 22 |
| `dispatcher_or_search_helper` | 86 |
| `duplicate_or_orientation_candidate` | 128 |
| `evidence_contract_gap` | 23 |
| `mathematical_leaf_law` | 127 |
| `proof_composition_or_recursive_strategy` | 28 |
| `target_abi_decision` | 8 |

## Required interpretation

- `mapped_not_kernel_checked` still needs an executable `.lit/.lean` tracer.
- `evidence_gap` uncatalogued rows need exact Result/certificate review.
- `unreachable` is an extractor finding, not a theorem about runtime reachability.
- Object rows are role-specific by design.
