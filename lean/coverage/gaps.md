# Direct Compiler Gap Report

Generated from the source-bound inventory. Object occurrence roles are
combined here; the JSON inventory keeps one row per role.

The 422 uncatalogued builtin identities are intentionally kept in
`uncatalogued_builtin_queue.tsv` and summarized by
`uncatalogued_mechanism_families.md`.

| Axis | Source identity | Status | Roles | Producers | Limitation / next gate |
| --- | --- | --- | --- | ---: | --- |
| `atomic_fact` | `AtomicFact::FnEqualFact` | `compiler_gap` | - | 23 | add one positive Result-driven tracer and direct compiler consumer for AtomicFact::FnEqualFact |
| `atomic_fact` | `AtomicFact::IsCartFact` | `compiler_gap` | - | 20 | add one positive Result-driven tracer and direct compiler consumer for AtomicFact::IsCartFact |
| `builtin_typed` | `matrix.expression_membership` | `abi_decision` | - | 1 | native matrix expressions do not yet have a reviewed Lean target ABI |
| `builtin_typed` | `nonzero.div` | `evidence_gap` | - | 2 | Litex.Same lacks the reviewed numeric-observation elimination required by division nonzero replay |
| `builtin_typed` | `nonzero.mul` | `evidence_gap` | - | 1 | Litex.Same lacks the reviewed numeric-observation elimination required by multiplication nonzero replay |
| `builtin_typed` | `not_equal.from_strict_order` | `evidence_gap` | - | 1 | strict-order inequality replay lacks a reviewed numeric-observation elimination |
| `builtin_typed` | `set.set_minus_infinite_of_infinite_finite` | `abi_decision` | - | 1 | the Lean target ABI does not yet represent infinite-set facts |
| `builtin_typed` | `set.subset_transitivity` | `compiler_gap` | - | 1 | add one positive Result-driven tracer and direct compiler consumer for set.subset_transitivity |
| `fact` | `Fact::ForallFactWithIff` | `compiler_gap` | - | 41 | add one positive Result-driven tracer and direct compiler consumer for Fact::ForallFactWithIff |
| `fact` | `Fact::NotForall` | `compiler_gap` | - | 28 | add one positive Result-driven tracer and direct compiler consumer for Fact::NotForall |
| `fact_proof` | `SuccessFactProofResult::DefinitionReduction` | `compiler_gap` | - | 4 | direct proof replay returns no proof for the legacy definition-reduction Result |
| `fact_proof` | `SuccessFactProofResult::DiagnosticOnly` | `evidence_gap` | - | 4 | a diagnostic-only successful Result retains no replayable proof evidence |
| `object` | `Obj::CartDim` | `compiler_gap` | `binder`, `definition_value`, `function_domain_or_codomain`, `target_set`, `term`, `well_definedness` | 25 | add one positive Result-driven tracer and direct compiler consumer for Obj::CartDim |
| `object` | `Obj::FiniteSetMax` | `compiler_gap` | `binder`, `definition_value`, `function_domain_or_codomain`, `target_set`, `term`, `well_definedness` | 38 | add one positive Result-driven tracer and direct compiler consumer for Obj::FiniteSetMax |
| `object` | `Obj::FiniteSetMin` | `compiler_gap` | `binder`, `definition_value`, `function_domain_or_codomain`, `target_set`, `term`, `well_definedness` | 38 | add one positive Result-driven tracer and direct compiler consumer for Obj::FiniteSetMin |
| `object` | `Obj::FiniteSetSize` | `compiler_gap` | `binder`, `definition_value`, `function_domain_or_codomain`, `target_set`, `term`, `well_definedness` | 66 | add one positive Result-driven tracer and direct compiler consumer for Obj::FiniteSetSize |
| `object` | `Obj::IndexIntersect` | `abi_decision` | `binder`, `definition_value`, `function_domain_or_codomain`, `target_set`, `term`, `well_definedness` | 41 | native indexed-intersection semantics are intentionally deferred |
| `object` | `Obj::IndexUnion` | `abi_decision` | `binder`, `definition_value`, `function_domain_or_codomain`, `target_set`, `term`, `well_definedness` | 43 | native indexed-union semantics are intentionally deferred |
| `object` | `Obj::MatrixAdd` | `abi_decision` | `binder`, `definition_value`, `function_domain_or_codomain`, `target_set`, `term`, `well_definedness` | 37 | native matrix expressions do not yet have a reviewed Lean target ABI |
| `object` | `Obj::MatrixListObj` | `abi_decision` | `binder`, `definition_value`, `function_domain_or_codomain`, `target_set`, `term`, `well_definedness` | 35 | native matrix expressions do not yet have a reviewed Lean target ABI |
| `object` | `Obj::MatrixMul` | `abi_decision` | `binder`, `definition_value`, `function_domain_or_codomain`, `target_set`, `term`, `well_definedness` | 38 | native matrix expressions do not yet have a reviewed Lean target ABI |
| `object` | `Obj::MatrixPow` | `abi_decision` | `binder`, `definition_value`, `function_domain_or_codomain`, `target_set`, `term`, `well_definedness` | 39 | native matrix expressions do not yet have a reviewed Lean target ABI |
| `object` | `Obj::MatrixScalarMul` | `abi_decision` | `binder`, `definition_value`, `function_domain_or_codomain`, `target_set`, `term`, `well_definedness` | 37 | native matrix expressions do not yet have a reviewed Lean target ABI |
| `object` | `Obj::MatrixSub` | `abi_decision` | `binder`, `definition_value`, `function_domain_or_codomain`, `target_set`, `term`, `well_definedness` | 37 | native matrix expressions do not yet have a reviewed Lean target ABI |
| `object` | `Obj::ObjAsStructInstanceWithFieldAccess` | `compiler_gap` | `binder`, `definition_value`, `function_domain_or_codomain`, `target_set`, `term`, `well_definedness` | 36 | add one positive Result-driven tracer and direct compiler consumer for Obj::ObjAsStructInstanceWithFieldAccess |
| `object` | `Obj::Proj` | `compiler_gap` | `binder`, `definition_value`, `function_domain_or_codomain`, `target_set`, `term`, `well_definedness` | 26 | add one positive Result-driven tracer and direct compiler consumer for Obj::Proj |
| `object` | `Obj::Quot` | `compiler_gap` | `binder`, `definition_value`, `function_domain_or_codomain`, `target_set`, `term`, `well_definedness` | 36 | object lowering explicitly rejects the builtin quot object |
| `object` | `Obj::Replacement` | `compiler_gap` | `binder`, `definition_value`, `function_domain_or_codomain`, `target_set`, `term`, `well_definedness` | 28 | add one positive Result-driven tracer and direct compiler consumer for Obj::Replacement |
| `object_atom` | `AtomObj::IdentifierWithMod` | `compiler_gap` | - | 30 | add one positive Result-driven tracer and direct compiler consumer for AtomObj::IdentifierWithMod |
| `tracer` | `71_CapturedPredicateSetBuilder.lit` | `unreachable` | - | 1 | decide whether to register 71_CapturedPredicateSetBuilder.lit or move it outside the configured examples module |
| `tracer` | `72_NamedFactTheorem.lit` | `unreachable` | - | 1 | decide whether to register 72_NamedFactTheorem.lit or move it outside the configured examples module |
| `well_definedness_result` | `SuccessVerifyTemplateDomainResult` | `compiler_gap` | - | 2 | add one positive Result-driven tracer and direct compiler consumer for SuccessVerifyTemplateDomainResult |
| `well_definedness_result` | `SuccessVerifyTemplateHeaderArgumentResult` | `compiler_gap` | - | 2 | add one positive Result-driven tracer and direct compiler consumer for SuccessVerifyTemplateHeaderArgumentResult |

Unique non-uncatalogued gap identities: **34**.
