use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::search_atomic_except_equality_fact_proof_by_builtin_rule_result::{PrimeFactSearchProofByBuiltinRule, NotPrimeFactSearchProofByBuiltinRule, CoprimeFactSearchProofByBuiltinRule, NotCoprimeFactSearchProofByBuiltinRule};
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
                AtomicExceptEqualityFactSearchedProof::ByKnownZeroRemainder(p) => self.compile_known_dvd_zero(&success.fact, p, position)?,
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
                    AtomicExceptEqualityFactSearchProofByBuiltinRule::IsFiniteSetFact(rule) => {
                        use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::is_finite_set::IsFiniteSetFactSearchProofByBuiltinRule;
                        let AtomicFact::IsFiniteSetFact(fact) = &success.fact else { return Err(LeanCompileError::unsupported("FiniteSet/FactSubject")); };
                        match rule {
                            IsFiniteSetFactSearchProofByBuiltinRule::ListSet(_) => self.compile_list_finite(&fact.set, position)?,
                            IsFiniteSetFactSearchProofByBuiltinRule::ClosedRange(_) if matches!(&fact.set,Obj::SetFormer(SetFormer::ClosedRange(_))) => format!("(Litex.closedRangeFinite {})",self.compile_object_reference(&fact.set,position)?),
                            IsFiniteSetFactSearchProofByBuiltinRule::Range(_) if matches!(&fact.set,Obj::SetFormer(SetFormer::Range(_))) => format!("(Litex.rangeFinite {})",self.compile_object_reference(&fact.set,position)?),
                            _ => return Err(LeanCompileError::unsupported("FiniteSet/Rule")),
                        }
                    },
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
                    AtomicExceptEqualityFactSearchProofByBuiltinRule::IsNonemptySetFact(IsNonemptySetFactSearchProofByBuiltinRule::LiteralListSetNonempty(_)) => {
                        let AtomicFact::IsNonemptySetFact(f) = &success.fact else { return Err(LeanCompileError::unsupported("Nonempty/LiteralSubject")); };
                        if !matches!(&f.set, Obj::SetFormer(SetFormer::ListSet(s)) if !s.list.is_empty()) {
                            return Err(LeanCompileError::unsupported("Nonempty/LiteralShape"));
                        }
                        format!("(Litex.insertNonempty {})", self.compile_object_reference(&f.set, position)?)
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
                    AtomicExceptEqualityFactSearchProofByBuiltinRule::NotEqualFact(crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::not_equal::NotEqualFactSearchProofByBuiltinRule::PeriodicTrigNonzero(p)) => self.compile_periodic_trig_nonzero(&success.fact,p,position)?,
                    AtomicExceptEqualityFactSearchProofByBuiltinRule::NotEqualFact(crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::not_equal::NotEqualFactSearchProofByBuiltinRule::ListSetDifferentLength(_)) => self.compile_list_distinct_lengths(&success.fact, position)?,
                    rule @ (AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(_) | AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterFact(_) | AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(_) | AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterEqualFact(_) | AtomicExceptEqualityFactSearchProofByBuiltinRule::NotEqualFact(_)) => self.compile_order_builtin(&success.fact, rule, position)?,
                    AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(rule) => match &success.fact {
                        AtomicFact::InFact(fact) => match rule {
                            InFactSearchProofByBuiltinRule::IndexUnionMembershipFromIndex(p) => self.compile_index_union_member(fact,p.cite_index_in_index_set_fact_id,&p.element_in_fiber_proof,position)?,
                            InFactSearchProofByBuiltinRule::IntervalMembership(p) => self.compile_real_interval_member(fact,&[&p.in_real_proof,&p.lower_bound_proof,&p.upper_bound_proof],position)?,
                            InFactSearchProofByBuiltinRule::OneSideInfinityIntervalMembership(p) => self.compile_real_interval_member(fact,&[&p.in_real_proof,&p.endpoint_bound_proof],position)?,
                            InFactSearchProofByBuiltinRule::NativeMatrix(p) => self.compile_matrix_membership(fact, p, position)?,
                            InFactSearchProofByBuiltinRule::NativeConstantMembership(p) => self.compile_native_constant_member(fact, &p.kind, position)?,
                            InFactSearchProofByBuiltinRule::AnonymousFnInDeclaredFnSet(_) => self.compile_literal_function_member(fact, position)?,
                            InFactSearchProofByBuiltinRule::CompositionApplicationInCodomain(p) => self.compile_composition_output(fact,p,position)?,
                            InFactSearchProofByBuiltinRule::CompositionInFunctionSet(p) => {
                                let Obj::FunctionSpace(FunctionSpace::FnSet(target)) = &fact.set else {
                                    return Err(LeanCompileError::unsupported("Composition/MembershipTarget"));
                                };
                                if !crate::execute::execute_fact_stmt::function_domain::function_domains_alpha_equal(&p.callable.function.body, target)
                                    || p.callable.function.body.ret_set.ir() != target.ret_set.ir() {
                                    return Err(LeanCompileError::unsupported("Composition/MembershipSignature"));
                                }
                                self.compile_composition_member(&fact.element, &p.callable, position)?
                            }
                            InFactSearchProofByBuiltinRule::PositiveRealProduct(_) | InFactSearchProofByBuiltinRule::PositiveRealQuotient(_) | InFactSearchProofByBuiltinRule::NonzeroRationalProduct(_) | InFactSearchProofByBuiltinRule::NonzeroRationalQuotient(_) => self.compile_refined_arithmetic_closure(fact, rule, position)?,
                            crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::in_fact::InFactSearchProofByBuiltinRule::ComplexArithmeticClosure(_) => self.compile_complex_arithmetic_closure(fact, position)?,
                            InFactSearchProofByBuiltinRule::RealPower(_) | InFactSearchProofByBuiltinRule::RealOperandArithmeticClosure(_) | InFactSearchProofByBuiltinRule::RealArithmeticConstructorClosure(_) => self.compile_real_arithmetic_membership(fact, rule, position)?,
                            InFactSearchProofByBuiltinRule::PredecessorFromPositiveNatural(p) => self.compile_natural_predecessor(fact, &p.in_natural_proof, &p.positive_proof, position)?,
                            InFactSearchProofByBuiltinRule::FiniteSetMaxMember(p) => self.compile_finite_extremum_member(fact, true, &p.set_equal, position)?,
                            InFactSearchProofByBuiltinRule::AggregateScalarCodomain(p) => self.compile_scalar_aggregate_member(fact, p, position)?,
                            InFactSearchProofByBuiltinRule::FoldScalarCodomain(p) => self.compile_fold_scalar_member(fact, p, position)?,
                            InFactSearchProofByBuiltinRule::FiniteSetMinMember(p) => self.compile_finite_extremum_member(fact, false, &p.set_equal, position)?,
                            InFactSearchProofByBuiltinRule::FiniteSetSubsetMembership(_) | InFactSearchProofByBuiltinRule::ListSetElementMembership(_) | InFactSearchProofByBuiltinRule::SetBuilderMembership(_) => self.compile_set_membership_rule(fact, rule, position)?,
                            InFactSearchProofByBuiltinRule::StructObjMembership(p) => self.compile_struct_membership(fact, p, position)?,
                            InFactSearchProofByBuiltinRule::CartMembership(p) => self.compile_cart_membership(fact, &p.domain, None, &p.proof_of_requirement_facts, position)?,
                            InFactSearchProofByBuiltinRule::PowerSetMembership(_) | InFactSearchProofByBuiltinRule::SetMinusMembership(_) | InFactSearchProofByBuiltinRule::IntersectMembership(_) | InFactSearchProofByBuiltinRule::UnionMembershipFromLeft(_) | InFactSearchProofByBuiltinRule::UnionMembershipFromRight(_) => self.compile_set_operator_membership(fact, rule, position)?,
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
                    AtomicExceptEqualityFactSearchProofByBuiltinRule::PrimeFact(PrimeFactSearchProofByBuiltinRule::PrimeByComputation(p)) => self.compile_closed_number_predicate(&success.fact, &[&p.resolved_value], position)?,
                    AtomicExceptEqualityFactSearchProofByBuiltinRule::NotPrimeFact(NotPrimeFactSearchProofByBuiltinRule::NotPrimeByComputation(p)) => self.compile_closed_number_predicate(&success.fact, &[&p.resolved_value], position)?,
                    AtomicExceptEqualityFactSearchProofByBuiltinRule::CoprimeFact(CoprimeFactSearchProofByBuiltinRule::CoprimeByComputation(p)) => self.compile_closed_number_predicate(&success.fact, &[&p.left_resolved, &p.right_resolved], position)?,
                    AtomicExceptEqualityFactSearchProofByBuiltinRule::NotCoprimeFact(NotCoprimeFactSearchProofByBuiltinRule::NotCoprimeByComputation(p)) => self.compile_closed_number_predicate(&success.fact, &[&p.left_resolved, &p.right_resolved], position)?,
                    AtomicExceptEqualityFactSearchProofByBuiltinRule::NotIsNonemptySetFact(crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::not_is_nonempty_set::NotIsNonemptySetFactSearchProofByBuiltinRule::EmptyListSet(_)) => {
                        let AtomicFact::NotIsNonemptySetFact(f) = &success.fact else {return Err(LeanCompileError::unsupported("Empty/Subject"))};
                        if !matches!(&f.set, Obj::SetFormer(SetFormer::ListSet(s)) if s.list.is_empty()) {return Err(LeanCompileError::unsupported("Empty/Shape"))}
                        "(Litex.emptyNotNonempty (M := M))".to_string()
                    },
                    AtomicExceptEqualityFactSearchProofByBuiltinRule::SupersetFact(rule) => {
                        use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::superset::SupersetFactSearchProofByBuiltinRule;
                        let AtomicFact::SupersetFact(f)=&success.fact else{return Err(LeanCompileError::unsupported("Superset/Subject"))};
                        match rule {
                            SupersetFactSearchProofByBuiltinRule::SupersetReflexivity(_) if f.left.ir()==f.right.ir() => format!("(Litex.subsetRefl {})", self.compile_object_reference(&f.left, position)?),
                            SupersetFactSearchProofByBuiltinRule::StandardSetSuperset(p) if f.left==Obj::StandardSet(p.left.clone()) && f.right==Obj::StandardSet(p.right.clone()) => {
                                let member=standard_inclusion_term(&p.right,&p.left,"_a","_ha")?;
                                format!("(Litex.subsetOfForall {} {} (fun _a _ha => {member}))",standard_term(&p.right)?,standard_term(&p.left)?)
                            },
                            _=>return Err(LeanCompileError::unsupported("Superset/RuleSubject")),
                        }
                    },
                    AtomicExceptEqualityFactSearchProofByBuiltinRule::NotIsFiniteSetFact(crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::not_is_finite_set::NotIsFiniteSetFactSearchProofByBuiltinRule::StandardInfiniteSet(_)) => {
                        let AtomicFact::NotIsFiniteSetFact(f)=&success.fact else{return Err(LeanCompileError::unsupported("InfiniteSet/Subject"))};
                        if f.set != Obj::StandardSet(StandardSet::N) {return Err(LeanCompileError::unsupported("InfiniteSet/Carrier"))}
                        "(Litex.naturalNotFinite (M := M))".to_string()
                    },
                    other => return Err(unsupported_atomic_builtin(other)),
                },
                AtomicExceptEqualityFactSearchedProof::ByKnownSpecialProperty(AtomicExceptEqualityFactSearchProofByKnownSpecialProperty::InFact(rule)) => match &success.fact {
                    AtomicFact::InFact(fact) => match rule {
                        InFactSearchProofByKnownSpecialProperty::UnionInPowerSet(_)
                        | InFactSearchProofByKnownSpecialProperty::IntersectInPowerSetFromLeft(_)
                        | InFactSearchProofByKnownSpecialProperty::IntersectInPowerSetFromRight(_)
                        | InFactSearchProofByKnownSpecialProperty::SetMinusInPowerSet(_)
                        | InFactSearchProofByKnownSpecialProperty::SetMinusInPowerSetOfLeft(_) => self.compile_power_set_closure(fact, rule, position)?,
                        InFactSearchProofByKnownSpecialProperty::ListSetInPowerSetFromMembers(_) => self.compile_power_set_closure(fact, rule, position)?,
                        InFactSearchProofByKnownSpecialProperty::FnApplicationInFnRange(proof) => self.compile_call_in_range(fact, proof, position)?,
                        InFactSearchProofByKnownSpecialProperty::FoldInCarrier(proof) => self.compile_fold_carrier_member(fact, proof, position)?,
                        InFactSearchProofByKnownSpecialProperty::PositiveRealFromKnownStrictOrder(proof) => self.compile_positive_real_from_known_strict_order(fact, proof, position)?,
                        _ => self.compile_fn_return_rule(fact, rule, position)?,
                    },
                    _ => return Err(LeanCompileError::new("FunctionReturn/Family", "A returned-membership rule has another source fact family.")),
                },
                AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::FunctionSetMembership(p)) => self.compile_function_set_strategy(&success.fact,p,position)?,
                AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::IntersectFiniteFromBoth(p)) => self.compile_finite_intersection(&success.fact,p,position)?,
                AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::IntersectFiniteFromLeft(p)) => self.compile_finite_intersection_from_left(&success.fact,p,position)?,
                AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::IntersectFiniteFromRight(p)) => self.compile_finite_intersection_from_right(&success.fact,p,position)?,
                AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::SymDiffMembershipLeft(p)) => self.compile_sym_diff_membership(&success.fact, &p.requirement_facts, &p.proof_of_requirement_facts, [true, false], position)?,
                AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::SymDiffMembershipRight(p)) => self.compile_sym_diff_membership(&success.fact, &p.requirement_facts, &p.proof_of_requirement_facts, [false, true], position)?,
                AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::SymDiffNonmembershipBoth(p)) => self.compile_sym_diff_membership(&success.fact, &p.requirement_facts, &p.proof_of_requirement_facts, [true, true], position)?,
                AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::SymDiffNonmembershipNeither(p)) => self.compile_sym_diff_membership(&success.fact, &p.requirement_facts, &p.proof_of_requirement_facts, [false, false], position)?,
                AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::ListSetSubsetFromMembers(p)) => {
                    let AtomicFact::SubsetFact(f)=&success.fact else{return Err(LeanCompileError::unsupported("ListSubset/StrategySubject"))};
                    if p.requirement_facts.len()!=p.proof_of_requirement_facts.len() {return Err(LeanCompileError::unsupported("ListSubset/StrategyArity"))}
                    for (fact,proof) in p.requirement_facts.iter().zip(&p.proof_of_requirement_facts) {
                        if source_subject(proof)? != *fact {return Err(LeanCompileError::unsupported("ListSubset/StrategyPremise"))}
                    }
                    self.compile_list_subset(f,&p.proof_of_requirement_facts,position)?
                },
                AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::PreimageMembership(p)) => self.compile_preimage_membership(&success.fact, false, &p.construction, &p.input_view, &p.requirement_facts, &p.proof_of_requirement_facts, position)?,
                AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::PreimageSetMembership(p)) => self.compile_preimage_membership(&success.fact, true, &p.construction, &p.input_view, &p.requirement_facts, &p.proof_of_requirement_facts, position)?,
                AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::IntervalMembership(p)) => {
                    let AtomicFact::InFact(fact)=&success.fact else{return Err(LeanCompileError::unsupported("RealInterval/StrategySubject"))};
                    if p.requirement_facts.len()!=p.proof_of_requirement_facts.len(){return Err(LeanCompileError::unsupported("RealInterval/StrategyStages"))}
                    for (fact,proof) in p.requirement_facts.iter().zip(&p.proof_of_requirement_facts){if &source_subject(proof)?!=fact{return Err(LeanCompileError::unsupported("RealInterval/StrategyPremise"))}}
                    self.compile_real_interval_member(fact,&p.proof_of_requirement_facts.iter().collect::<Vec<_>>(),position)?
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
                AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(strategy @ (
                    AtomicExceptEqualityFactSearchProofByBuiltinStrategy::AddComponentwiseLessEqual(_)
                    | AtomicExceptEqualityFactSearchProofByBuiltinStrategy::AddCrossedLessEqual(_)
                    | AtomicExceptEqualityFactSearchProofByBuiltinStrategy::AddComponentwiseStrictLeft(_)
                    | AtomicExceptEqualityFactSearchProofByBuiltinStrategy::AddComponentwiseStrictRight(_)
                )) => self.compile_componentwise_additive_order(&success.fact, strategy, position)?,
                AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(strategy @ (
                    AtomicExceptEqualityFactSearchProofByBuiltinStrategy::SubSharedSubtrahendLessEqual(_)
                    | AtomicExceptEqualityFactSearchProofByBuiltinStrategy::SubSharedMinuendLessEqual(_)
                    | AtomicExceptEqualityFactSearchProofByBuiltinStrategy::SubSharedSubtrahendLess(_)
                    | AtomicExceptEqualityFactSearchProofByBuiltinStrategy::SubSharedMinuendLess(_)
                )) => self.compile_shared_subtraction_order(&success.fact, strategy, position)?,
                AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::AddRightStrictShiftLeftWeak(proof)) =>
                    self.compile_add_strict_shift(&success.fact, &proof.requirement_facts, &proof.proof_of_requirement_facts, position)?,
                AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::CommonPositiveFactorLess(proof)) =>
                    self.compile_strict_mul_strategy(&success.fact, &proof.requirement_facts, &proof.proof_of_requirement_facts, position)?,
                AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::UnionSubsetFromBothOperands(p)) =>
                    self.compile_union_upper_bound_strategy(&success.fact, &p.requirement_facts, &p.proof_of_requirement_facts, position)?,
                AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::SetMinusSubsetFromLeft(p)) =>
                    self.compile_set_minus_upper_bound_strategy(&success.fact, &p.requirement_facts, &p.proof_of_requirement_facts, position)?,
                AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::IntersectSubsetFromLeftOperand(p)) =>
                    self.compile_intersection_subset_strategy(&success.fact, &p.requirement_facts, &p.proof_of_requirement_facts, true, position)?,
                AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::IntersectSubsetFromRightOperand(p)) =>
                    self.compile_intersection_subset_strategy(&success.fact, &p.requirement_facts, &p.proof_of_requirement_facts, false, position)?,
                AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::SetMinusMembership(p)) =>
                    self.compile_set_minus_membership_strategy(&success.fact, &p.requirement_facts, &p.proof_of_requirement_facts, position)?,
                AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::IntersectMembership(p)) =>
                    self.compile_intersection_membership_strategy(&success.fact, &p.requirement_facts, &p.proof_of_requirement_facts, position)?,
                AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::SubsetOfIntersectFromBothBounds(p)) =>
                    self.compile_subset_into_intersection(&success.fact, &p.requirement_facts, &p.proof_of_requirement_facts, position)?,
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
