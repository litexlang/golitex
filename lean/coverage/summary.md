# StmtResult-to-Lean Coverage Summary

Generated deterministically from current source by `build_inventory.py`.
A source/compiler reference is not a real Lean kernel acceptance result.

Total rows: **1453**

Source fingerprint (SHA-256): `324d0ac2dc704c14629edb93c6fe7f17a2c9d867a152d808f486dfde62dfe995`

## Rows by axis

| Axis | Rows |
| --- | ---: |
| `atomic_fact` | 30 |
| `builtin_typed` | 200 |
| `builtin_uncatalogued` | 423 |
| `fact` | 8 |
| `fact_proof` | 11 |
| `inference` | 25 |
| `object` | 492 |
| `object_atom` | 3 |
| `statement` | 63 |
| `statement_result` | 63 |
| `tracer` | 71 |
| `well_definedness_result` | 64 |

## Rows by status

| Status | Rows |
| --- | ---: |
| `abi_decision` | 58 |
| `compiler_gap` | 58 |
| `dead_or_duplicate_candidate` | 16 |
| `evidence_gap` | 400 |
| `kernel_checked` | 1 |
| `mapped_not_kernel_checked` | 917 |
| `unreachable` | 3 |

## Rows by owner

- Codex implementation/evidence rows: **1393**
- User semantic-decision rows: **60**

Repeated role rows are collapsed into the seven questions in the Day 1 user decision packet.

## Tracer obligations

- Existing source tracers: **71**
- Required per-route tracers: **1365**
- Not applicable until reachability/dead-code resolution: **17**

A `required` string is an explicit obligation, not a claim that the tracer already exists.

## Status by axis

| Axis | `abi_decision` | `compiler_gap` | `dead_or_duplicate_candidate` | `evidence_gap` | `kernel_checked` | `mapped_not_kernel_checked` | `unreachable` |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `atomic_fact` | 0 | 3 | 0 | 0 | 0 | 27 | 0 |
| `builtin_typed` | 2 | 1 | 0 | 3 | 0 | 194 | 0 |
| `builtin_uncatalogued` | 8 | 0 | 16 | 396 | 0 | 2 | 1 |
| `fact` | 0 | 2 | 0 | 0 | 0 | 6 | 0 |
| `fact_proof` | 0 | 1 | 0 | 1 | 0 | 9 | 0 |
| `inference` | 0 | 0 | 0 | 0 | 0 | 25 | 0 |
| `object` | 48 | 48 | 0 | 0 | 0 | 396 | 0 |
| `object_atom` | 0 | 1 | 0 | 0 | 0 | 2 | 0 |
| `statement` | 0 | 0 | 0 | 0 | 0 | 63 | 0 |
| `statement_result` | 0 | 0 | 0 | 0 | 0 | 63 | 0 |
| `tracer` | 0 | 0 | 0 | 0 | 1 | 68 | 2 |
| `well_definedness_result` | 0 | 2 | 0 | 0 | 0 | 62 | 0 |

## Lean adapter surface

- Compiler-emitted literal `Litex.*` symbols: **262**
- Interpolated Lean symbol templates: **10**
- Interpolated compiler call sites: **48**
- Dynamic sites with a function-local certificate match: **18**
- Dynamic sites selected by an enclosing caller/helper route: **30**
- Builtin IDs with a function-local Lean candidate: **144**
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
| `selected_semantic_child` | 87 |
| `shared_adapter_candidate` | 128 |
| `typed_certificate_route` | 194 |

## Builtin identity reconciliation

- Stable rule IDs in source: **623**
- Typed/catalogued IDs: **200**
- Uncatalogued IDs: **423**
- Uncatalogued IDs with a direct production reference: **406**
- Uncatalogued IDs without a direct production reference: **17**
- User-owned ABI decisions: **10**
- Codex-owned implementation/evidence rows: **613**

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
| `dispatcher_or_search_helper` | 87 |
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
