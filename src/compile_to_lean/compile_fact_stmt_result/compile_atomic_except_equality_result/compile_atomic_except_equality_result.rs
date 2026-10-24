use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::in_fact::InFactSearchProofByBuiltinRule;
use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_known_special_property::{AtomicExceptEqualityFactSearchProofByKnownSpecialProperty, InFactSearchProofByKnownSpecialProperty};
use crate::prelude::*;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::VerifyAtomicExceptEqualityFactSuccess;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_verify_atomic_except_equality_result(
        &self,
        result: &VerifyAtomicExceptEqualityFactResult,
        position: &SourcePosition<'_>,
    ) -> Result<(String, String), LeanCompileError> {
        match result {
            VerifyAtomicExceptEqualityFactResult::Success(success) => {
                self.compile_atomic_success_body(success, position)
            }
            VerifyAtomicExceptEqualityFactResult::Failed(_) => Err(LeanCompileError::new(
                "Atomic/Failed",
                "Failed verification is not proof evidence.",
            )),
        }
    }

    pub(in crate::compile_to_lean) fn compile_verify_atomic_success(
        &self,
        success: &VerifyAtomicExceptEqualityFactSuccess,
        position: &SourcePosition<'_>,
    ) -> Result<(String, String), LeanCompileError> {
        let source = SourcePosition::new(Some(position), SourceOwner::AtomicVerify(success), 0);
        self.compile_atomic_success_body(success, &source)
    }

    fn compile_atomic_success_body(
        &self,
        success: &VerifyAtomicExceptEqualityFactSuccess,
        position: &SourcePosition<'_>,
    ) -> Result<(String, String), LeanCompileError> {
        let bindings =
            self.compile_atomic_wd_locals(&success.well_defined_proof, &success.fact, position)?;
        let locals = SourcePosition::new(
            position.parent,
            SourceOwner::AtomicWDLocals(
                &success.well_defined_proof,
                success
                    .well_defined_proof
                    .well_defined_of_each_parameter
                    .len(),
            ),
            usize::MAX,
        );
        let formed = SourcePosition {
            parent: Some(&locals),
            before: usize::MAX,
            ..*position
        };
        let position = &formed;
        let proposition = self.atomic_proposition(&success.fact, position)?;
        let proof = match &success.searched_proof {
                AtomicExceptEqualityFactSearchedProof::ByTemplateMembership(_) => {
                    return Err(LeanCompileError::unsupported("Atomic/TemplateMembership"));
                }
                AtomicExceptEqualityFactSearchedProof::ByKnownZeroRemainder(_) => {
                    return Err(LeanCompileError::unsupported("Atomic/KnownZeroRemainder"));
                }
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
                AtomicExceptEqualityFactSearchedProof::ByClosedCalculation(ClosedAtomicExceptEqualityCalculationProof::NotIn(proof)) => match &success.fact {
                    AtomicFact::NotInFact(fact) => self.compile_closed_nonmembership(fact, proof, position)?,
                    _ => return Err(LeanCompileError::unsupported("NotIn/ClosedFamily")),
                },
                AtomicExceptEqualityFactSearchedProof::ByClosedCalculation(ClosedAtomicExceptEqualityCalculationProof::NotEqual(proof)) =>
                    self.compile_closed_not_equal(&success.fact, proof, position)?,
                AtomicExceptEqualityFactSearchedProof::ByClosedCalculation(certificate @ (ClosedAtomicExceptEqualityCalculationProof::Less(_) | ClosedAtomicExceptEqualityCalculationProof::Greater(_) | ClosedAtomicExceptEqualityCalculationProof::LessEqual(_) | ClosedAtomicExceptEqualityCalculationProof::GreaterEqual(_) | ClosedAtomicExceptEqualityCalculationProof::NotLess(_) | ClosedAtomicExceptEqualityCalculationProof::NotGreater(_) | ClosedAtomicExceptEqualityCalculationProof::NotLessEqual(_) | ClosedAtomicExceptEqualityCalculationProof::NotGreaterEqual(_))) => self.compile_closed_order(&success.fact, certificate, position)?,
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
                        if p.target_set == StandardSet::RPos {
                            "(Litex.rPosNonempty (M := M))".to_string()
                        } else if p.target_set == StandardSet::NPos {
                            "(Litex.nPosNonempty (M := M))".to_string()
                        } else if let Some((_, name)) = numeric_refinement(&p.target_set) {
                            format!("(Litex.{}{}Nonempty (M := M))", name[..1].to_lowercase(), &name[1..])
                        } else {
                            format!("(Litex.standardNonempty (M := M) Litex.StandardSetValue.{})", standard_value_constructor(&p.target_set)?)
                        }
                    },
                    rule @ (AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(_) | AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterFact(_) | AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(_) | AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterEqualFact(_) | AtomicExceptEqualityFactSearchProofByBuiltinRule::NotEqualFact(_)) => self.compile_order_builtin(&success.fact, rule, position)?,
                    AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(rule) => match &success.fact {
                        AtomicFact::InFact(fact) => match rule {
                            InFactSearchProofByBuiltinRule::PositiveRealProduct(_) | InFactSearchProofByBuiltinRule::PositiveRealQuotient(_) | InFactSearchProofByBuiltinRule::NonzeroRationalProduct(_) | InFactSearchProofByBuiltinRule::NonzeroRationalQuotient(_) => self.compile_refined_arithmetic_closure(fact, rule, position)?,
                            crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::in_fact::InFactSearchProofByBuiltinRule::ComplexArithmeticClosure(_) => self.compile_complex_arithmetic_closure(fact, position)?,
                            InFactSearchProofByBuiltinRule::RealPower(_) | InFactSearchProofByBuiltinRule::RealOperandArithmeticClosure(_) | InFactSearchProofByBuiltinRule::RealArithmeticConstructorClosure(_) => self.compile_real_arithmetic_membership(fact, rule, position)?,
                            InFactSearchProofByBuiltinRule::PredecessorFromPositiveNatural(p) => self.compile_natural_predecessor(fact, &p.in_natural_proof, &p.positive_proof, position)?,
                            InFactSearchProofByBuiltinRule::FiniteSetSubsetMembership(_) | InFactSearchProofByBuiltinRule::ListSetElementMembership(_) | InFactSearchProofByBuiltinRule::SetBuilderMembership(_) => self.compile_set_membership_rule(fact, rule, position)?,
                            InFactSearchProofByBuiltinRule::CartMembership(p) => self.compile_cart_membership(fact, &p.domain, None, &p.proof_of_requirement_facts, position)?,
                            InFactSearchProofByBuiltinRule::PowerSetMembership(_) | InFactSearchProofByBuiltinRule::UnionMembershipFromLeft(_) | InFactSearchProofByBuiltinRule::UnionMembershipFromRight(_) => self.compile_set_operator_membership(fact, rule, position)?,
                            InFactSearchProofByBuiltinRule::AnonymousFnApplicationInFnRange(p) => self.compile_anonymous_call_in_range(fact, &p.function_equal, position)?,
                            _ => self.compile_fn_return_builtin(fact, rule, position)?,
                        },
                        _ => return Err(LeanCompileError::new("FunctionReturn/Family", "A returned-membership rule has another source fact family.")),
                    },
                    AtomicExceptEqualityFactSearchProofByBuiltinRule::SubsetFact(rule) => match &success.fact {
                        AtomicFact::SubsetFact(fact) => self.compile_set_subset_rule(fact, rule, position)?,
                        _ => return Err(LeanCompileError::new("Set/SubsetFamily", "Subset evidence belongs to another atomic family.")),
                    },
                    AtomicExceptEqualityFactSearchProofByBuiltinRule::NotInFact(rule) => match &success.fact {
                        AtomicFact::NotInFact(fact) => self.compile_nonmembership_builtin(fact, rule, position)?,
                        _ => return Err(LeanCompileError::unsupported("NotIn/FactFamily")),
                    },
                    rule @ (AtomicExceptEqualityFactSearchProofByBuiltinRule::NotGreaterFact(_) | AtomicExceptEqualityFactSearchProofByBuiltinRule::NotLessFact(_) | AtomicExceptEqualityFactSearchProofByBuiltinRule::NotGreaterEqualFact(_) | AtomicExceptEqualityFactSearchProofByBuiltinRule::NotLessEqualFact(_)) => self.compile_negative_order_builtin(&success.fact, rule, position)?,
                    other => return Err(unsupported_atomic_builtin(other)),
                },
                AtomicExceptEqualityFactSearchedProof::ByKnownSpecialProperty(AtomicExceptEqualityFactSearchProofByKnownSpecialProperty::InFact(rule)) => match &success.fact {
                    AtomicFact::InFact(fact) => match rule {
                        InFactSearchProofByKnownSpecialProperty::FnApplicationInFnRange(proof) => self.compile_call_in_range(fact, proof, position)?,
                        InFactSearchProofByKnownSpecialProperty::PositiveRealFromKnownStrictOrder(proof) => self.compile_positive_real_from_known_strict_order(fact, proof, position)?,
                        _ => self.compile_fn_return_rule(fact, rule, position)?,
                    },
                    _ => return Err(LeanCompileError::new("FunctionReturn/Family", "A returned-membership rule has another source fact family.")),
                },
                AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::NonzeroProduct(proof)) =>
                    self.compile_nonzero_product(&success.fact, &proof.requirement_facts, &proof.proof_of_requirement_facts, position)?,
                AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::SubNonnegativeFromZero(proof)) =>
                    self.compile_sub_nonnegative_strategy(&success.fact, &proof.requirement_facts, &proof.proof_of_requirement_facts, position)?,
                AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(strategy @ (AtomicExceptEqualityFactSearchProofByBuiltinStrategy::NonnegativeSumIsNonnegative(_) | AtomicExceptEqualityFactSearchProofByBuiltinStrategy::StrictAdditiveLeftStrict(_) | AtomicExceptEqualityFactSearchProofByBuiltinStrategy::StrictAdditiveRightStrict(_) | AtomicExceptEqualityFactSearchProofByBuiltinStrategy::ProductNonnegativeBothNonneg(_))) =>
                    self.compile_selected_zero_bound_strategy(&success.fact, strategy, position)?,
                AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::DivSharedPositiveDenomLessEqual(proof)) =>
                    self.compile_div_monotone_strategy(&success.fact, &proof.requirement_facts, &proof.proof_of_requirement_facts, position)?,
                AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::RefinedNumericCarrier(proof)) => match &success.fact {
                    AtomicFact::InFact(fact) => self.compile_refined_numeric_strategy(fact, &proof.requirement_facts, &proof.proof_of_requirement_facts, position)?,
                    _ => return Err(LeanCompileError::new("RefinedNumericCarrier/Family", "The selected numeric refinement has another atomic source family.")),
                },
                AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(strategy @ (AtomicExceptEqualityFactSearchProofByBuiltinStrategy::PosAddPosIsPos(_) | AtomicExceptEqualityFactSearchProofByBuiltinStrategy::QuotientPositiveSameSignPos(_) | AtomicExceptEqualityFactSearchProofByBuiltinStrategy::ProductPositiveBothPos(_))) =>
                    self.compile_positive_order_strategy(&success.fact, strategy, position)?,
                AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::CartMembership(proof)) => match &success.fact {
                    AtomicFact::InFact(fact) => self.compile_cart_membership(fact, &proof.domain, Some(&proof.requirement_facts), &proof.proof_of_requirement_facts, position)?,
                    _ => return Err(LeanCompileError::new("CartMembership/Family", "Cartesian membership evidence has another source fact family.")),
                },
                AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::PowerSetMembership(proof)) => match &success.fact {
                    AtomicFact::InFact(fact) => self.compile_power_set_membership_strategy(fact, proof, position)?,
                    _ => return Err(LeanCompileError::new("PowerSet/Family", "Power-set membership evidence has another source fact family.")),
                },
                AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::PowSharedExponentLessEqual(proof)) =>
                    self.compile_power_weak_order_strategy(&success.fact, &proof.requirement_facts, &proof.proof_of_requirement_facts, position)?,
                AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(strategy @ (
                    AtomicExceptEqualityFactSearchProofByBuiltinStrategy::AddRightNonnegativeShiftLeft(_)
                    | AtomicExceptEqualityFactSearchProofByBuiltinStrategy::AddRightNonnegativeShiftRight(_)
                    | AtomicExceptEqualityFactSearchProofByBuiltinStrategy::AddLeftNonpositiveShiftLeft(_)
                    | AtomicExceptEqualityFactSearchProofByBuiltinStrategy::AddLeftNonpositiveShiftRight(_)
                )) => self.compile_weak_additive_shift(&success.fact, strategy, position)?,
                AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::AddRightStrictShiftLeftWeak(proof)) =>
                    self.compile_add_strict_shift(&success.fact, &proof.requirement_facts, &proof.proof_of_requirement_facts, position)?,
                AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::CommonPositiveFactorLess(proof)) =>
                    self.compile_strict_mul_strategy(&success.fact, &proof.requirement_facts, &proof.proof_of_requirement_facts, position)?,
                AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::UnionMembershipFromLeft(proof)) =>
                    self.compile_union_membership_strategy(&success.fact, &proof.requirement_facts, &proof.proof_of_requirement_facts, true, position)?,
                AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::CartNonemptyFromAllFactors(proof)) =>
                    self.compile_cart_nonempty_strategy(&success.fact, &proof.requirement_facts, &proof.proof_of_requirement_facts, position)?,
                AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::FiniteFunctionApplicationMembership(proof)) =>
                    self.compile_finite_application_membership(&success.fact, &proof.source, proof.index, &proof.requirement_facts, &proof.proof_of_requirement_facts, position)?,
                AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::UnionMembershipFromRight(proof)) =>
                    self.compile_union_membership_strategy(&success.fact, &proof.requirement_facts, &proof.proof_of_requirement_facts, false, position)?,
                AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(_) => {
                    return Err(LeanCompileError::new("Atomic/BuiltinStrategy", &format!("Unsupported selected strategy for `{}`.", success.fact.readable_string())))
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
                AtomicExceptEqualityFactSearchedProof::ByKnownRewrite(proof) =>
                    self.compile_registered_rewrite(&success.fact, proof, position)?,
            };

        if bindings.is_empty() {
            Ok((proposition, proof))
        } else {
            let bindings = bindings.join("\n").replace('\n', "\n  ");
            Ok((
                format!(
                    "(by\n  {bindings}\n  exact {})",
                    proposition.replace('\n', "\n  ")
                ),
                format!(
                    "(by\n  {bindings}\n  exact {})",
                    proof.replace('\n', "\n  ")
                ),
            ))
        }
    }
}
