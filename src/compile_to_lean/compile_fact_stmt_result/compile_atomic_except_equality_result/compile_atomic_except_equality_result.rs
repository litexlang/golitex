use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::in_fact::InFactSearchProofByBuiltinRule;
use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::AtomicExceptEqualityFactSearchProofByKnownSpecialProperty;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_verify_atomic_except_equality_result(
        &self,
        result: &VerifyAtomicExceptEqualityFactResult,
        position: &SourcePosition<'_>,
    ) -> Result<(String, String), LeanCompileError> {
        match result {
            VerifyAtomicExceptEqualityFactResult::Success(success) => {
                self.compile_atomic_wd(&success.well_defined_proof, &success.fact, position)?;
                let formed = SourcePosition {
                    before: usize::MAX,
                    ..*position
                };
                let position = &formed;
                let proposition = self.atomic_proposition(&success.fact, position)?;
                let proof = match &success.searched_proof {
                        AtomicExceptEqualityFactSearchedProof::ByStructuralMembership(proof) => {
                            match &success.fact {
                                AtomicFact::InFact(fact)
                                    if fact.element.ir() == proof.element.ir()
                                        && fact.set.ir()
                                            == Obj::StandardSet(proof.set.clone()).ir() => {}
                                _ => {
                                    return Err(LeanCompileError::new(
                                        "StructuralMembership",
                                        "Evidence does not describe the verified membership.",
                                    ))
                                }
                            }
                            self.compile_structural(proof, position)?
                        }
                        AtomicExceptEqualityFactSearchedProof::ByClosedCalculation(
                            ClosedAtomicExceptEqualityCalculationProof::In(proof),
                        ) => match &success.fact {
                            AtomicFact::InFact(fact) => {
                                self.compile_closed_membership(&fact.element, &fact.set, proof, position)?
                            }
                            _ => {
                                return Err(LeanCompileError::new(
                                    "ClosedMembership",
                                    "Membership calculation has another fact family.",
                                ))
                            }
                        },
                        AtomicExceptEqualityFactSearchedProof::ByClosedCalculation(ClosedAtomicExceptEqualityCalculationProof::NotEqual(proof)) =>
                            self.compile_closed_not_equal(&success.fact, proof, position)?,
                        AtomicExceptEqualityFactSearchedProof::ByClosedCalculation(certificate @ (ClosedAtomicExceptEqualityCalculationProof::Less(_) | ClosedAtomicExceptEqualityCalculationProof::Greater(_) | ClosedAtomicExceptEqualityCalculationProof::LessEqual(_) | ClosedAtomicExceptEqualityCalculationProof::GreaterEqual(_))) => self.compile_closed_order(&success.fact, certificate, position)?,
                        AtomicExceptEqualityFactSearchedProof::ByClosedCalculation(_) => {
                            return Err(LeanCompileError::unsupported(
                                "Atomic/ClosedCalculationNonMembership",
                            ))
                        }
                        AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(proof) => {
                            self.compile_known_atomic(proof, &success.fact, position)?
                        }
                        AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(rule) => match rule {
                            AtomicExceptEqualityFactSearchProofByBuiltinRule::IsSetFact(
                                IsSetFactSearchProofByBuiltinRule::AlwaysTrue(_),
                            ) => match &success.fact {
                                AtomicFact::IsSetFact(fact) => {
                                    format!("(Litex.isSet {})", self.compile_object_reference(&fact.set, position)?)
                                }
                                _ => {
                                    return Err(LeanCompileError::new(
                                        "IsSetAlwaysTrue",
                                        "Sethood evidence has another fact family.",
                                    ))
                                }
                            },
                            AtomicExceptEqualityFactSearchProofByBuiltinRule::IsNonemptySetFact(IsNonemptySetFactSearchProofByBuiltinRule::StandardSetNonempty(p)) => {
                                match &success.fact {
                                    AtomicFact::IsNonemptySetFact(f) if f.set == Obj::StandardSet(p.target_set.clone()) => {},
                                    _ => return Err(LeanCompileError::new("Nonempty/Subject", "Standard nonempty evidence describes another target.")),
                                }
                                standard_term(&p.target_set)?;
                                format!("(Litex.standardNonempty (M := M) Litex.StandardSetValue.{})", standard_value_constructor(&p.target_set)?)
                            },
                            rule @ (AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(_) | AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterFact(_) | AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(_) | AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterEqualFact(_) | AtomicExceptEqualityFactSearchProofByBuiltinRule::NotEqualFact(_)) => self.compile_order_builtin(&success.fact, rule, position)?,
                            AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(rule) => match &success.fact {
                                AtomicFact::InFact(fact) => match rule {
                                    crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::in_fact::InFactSearchProofByBuiltinRule::ComplexArithmeticClosure(_) => self.compile_complex_arithmetic_closure(fact, position)?,
                                    InFactSearchProofByBuiltinRule::ListSetElementMembership(_) | InFactSearchProofByBuiltinRule::SetBuilderMembership(_) => self.compile_set_membership_rule(fact, rule, position)?,
                                    _ => self.compile_fn_return_builtin(fact, rule, position)?,
                                },
                                _ => return Err(LeanCompileError::new("FunctionReturn/Family", "A returned-membership rule has another source fact family.")),
                            },
                            AtomicExceptEqualityFactSearchProofByBuiltinRule::SubsetFact(rule) => match &success.fact {
                                AtomicFact::SubsetFact(fact) => self.compile_set_subset_rule(fact, rule, position)?,
                                _ => return Err(LeanCompileError::new("Set/SubsetFamily", "Subset evidence belongs to another atomic family.")),
                            },
                            other => return Err(unsupported_atomic_builtin(other)),
                        },
                        AtomicExceptEqualityFactSearchedProof::ByKnownSpecialProperty(AtomicExceptEqualityFactSearchProofByKnownSpecialProperty::InFact(rule)) => match &success.fact {
                            AtomicFact::InFact(fact) => self.compile_fn_return_rule(fact, rule, position)?,
                            _ => return Err(LeanCompileError::new("FunctionReturn/Family", "A returned-membership rule has another source fact family.")),
                        },
                        AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::NonzeroProduct(proof)) =>
                            self.compile_nonzero_product(&success.fact, &proof.requirement_facts, &proof.proof_of_requirement_facts, position)?,
                        AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(_) => {
                            return Err(LeanCompileError::unsupported("Atomic/BuiltinStrategy"))
                        }
                        AtomicExceptEqualityFactSearchedProof::ByKnownStrategy(_) => {
                            return Err(LeanCompileError::unsupported("Atomic/KnownStrategy"))
                        }
                        AtomicExceptEqualityFactSearchedProof::ByDefinition(proof) =>
                            self.compile_prop_definition(&success.fact, proof, position)?,
                        AtomicExceptEqualityFactSearchedProof::ByKnownForallFact(proof) =>
                            self.compile_known_application(&success.fact.clone().into(), proof, position)?.1,
                        AtomicExceptEqualityFactSearchedProof::ByBuiltinRewrite(proof) =>
                            self.compile_atomic_builtin_rewrite(&success.fact, proof, position)?,
                        AtomicExceptEqualityFactSearchedProof::ByKnownRewrite(_) => {
                            return Err(LeanCompileError::unsupported("Atomic/KnownRewrite"))
                        }
                    };

                Ok((proposition, proof))
            }
            VerifyAtomicExceptEqualityFactResult::Failed(_) => Err(LeanCompileError::new(
                "Atomic/Failed",
                "Failed verification is not proof evidence.",
            )),
        }
    }
}
