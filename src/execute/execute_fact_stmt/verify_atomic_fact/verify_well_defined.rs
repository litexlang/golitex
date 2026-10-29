use super::well_defined_result::FunctionLimitApproachRealProof;
use crate::ast::fact::AtomicFact;
use crate::ast::obj::LimitApproach;
use crate::ast::obj::Obj;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::VerifyEqualFactWellDefinedResult;
use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::{
    AtomicFactWellDefinedProof, DetailedAtomicFactWellDefinedProof,
    FailToVerifyAtomicFactWellDefinedResult, PredicateDomainProof,
    PredicateSignatureWellDefinedFailure, PredicateSignatureWellDefinedProof,
    VerifyAtomicFactWellDefinedResult,
};
use crate::execute::execute_fact_stmt::well_defined_results::VerifyObjWellDefinedResult;
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::{Runtime, RuntimeError, RuntimeResult};

impl Runtime {
    // Atomic-except-equality only. EqualFact uses verify_equal_fact_well_definedness.
    // WD each argument object, then resolve the predicate signature.
    // First soft-missing argument → Failed; otherwise Success with proof.
    pub fn verify_atomic_fact_well_definedness(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyAtomicFactWellDefinedResult> {
        if matches!(fact, AtomicFact::EqualFact(_)) {
            return Err(RuntimeError::InternalBug(
                "EqualFact well-definedness must use verify_equal_fact_well_definedness"
                    .to_string(),
            ));
        }
        let args = atomic_except_equality_fact_arg_objs(fact);
        let mut succeeded_args = Vec::new();
        for arg in &args {
            match self.verify_obj_well_definedness(arg, verify_state.clone())? {
                VerifyObjWellDefinedResult::Failed { reason, .. } => {
                    return Ok(VerifyAtomicFactWellDefinedResult::Failed(
                        FailToVerifyAtomicFactWellDefinedResult::Argument {
                            fact: fact.clone(),
                            reason,
                        },
                    ));
                }
                VerifyObjWellDefinedResult::Success(proof) => {
                    self.result_detail()
                        .require(proof.detail(), "atomic WD argument")?;
                    if self.result_detail() == crate::result_detail::OutputDetail::Detailed {
                        succeeded_args.push(proof);
                    }
                }
            }
        }

        // A checked goal may not borrow a declaration from its later proof
        // body. For example, `claim: ? $chosen(0)` must fail here if chosen
        // has not been declared, even if the body defines it locally.
        let user_signature = match fact {
            AtomicFact::NormalAtomicFact(normal) => Some((&normal.predicate, normal.body.len())),
            AtomicFact::NotNormalAtomicFact(normal) => Some((&normal.predicate, normal.body.len())),
            _ => None,
        };
        let predicate_signature = match user_signature {
            Some((predicate, actual_arity)) => {
                let builtin_arity = match predicate {
                    crate::ast::names::AtomicName::Plain { name } => {
                        crate::builtin_theorem::builtin_certificate_arity(name)
                    }
                    _ => None,
                };
                let signature = if builtin_arity.is_some() {
                    PredicateSignatureWellDefinedProof::Builtin
                } else if let Some(def) = self.def_prop_visible(predicate) {
                    PredicateSignatureWellDefinedProof::Prop {
                        predicate: predicate.clone(),
                        arity: def
                            .typed_parameters
                            .groups
                            .iter()
                            .map(|g| g.params.len())
                            .sum(),
                    }
                } else if let Some(def) = self.def_abstract_prop_visible(predicate) {
                    PredicateSignatureWellDefinedProof::AbstractProp {
                        predicate: predicate.clone(),
                        arity: def.params.len(),
                    }
                } else {
                    return Ok(VerifyAtomicFactWellDefinedResult::Failed(
                        FailToVerifyAtomicFactWellDefinedResult::Predicate {
                            fact: fact.clone(),
                            well_defined_of_each_parameter: succeeded_args,
                            reason: PredicateSignatureWellDefinedFailure::Undefined {
                                predicate: predicate.clone(),
                            },
                        },
                    ));
                };
                let arity = match &signature {
                    PredicateSignatureWellDefinedProof::Prop { arity, .. }
                    | PredicateSignatureWellDefinedProof::AbstractProp { arity, .. } => *arity,
                    PredicateSignatureWellDefinedProof::Builtin => {
                        builtin_arity.expect("resolved builtin certificate signature")
                    }
                };
                if arity != actual_arity {
                    return Ok(VerifyAtomicFactWellDefinedResult::Failed(
                        FailToVerifyAtomicFactWellDefinedResult::Predicate {
                            fact: fact.clone(),
                            well_defined_of_each_parameter: succeeded_args,
                            reason: PredicateSignatureWellDefinedFailure::Arity {
                                predicate: predicate.clone(),
                                expected: arity,
                                actual: actual_arity,
                            },
                        },
                    ));
                }
                signature
            }
            _ => PredicateSignatureWellDefinedProof::Builtin,
        };
        if let Some(cite) = self.lookup_known_atomic_fact(fact) {
            return Ok(VerifyAtomicFactWellDefinedResult::Success(
                AtomicFactWellDefinedProof::new(self.result_detail(), || {
                    DetailedAtomicFactWellDefinedProof {
                        well_defined_of_each_parameter: succeeded_args,
                        predicate_signature,
                        predicate_domain: PredicateDomainProof::ByKnownFact(cite),
                    }
                })?,
            ));
        }
        let multi_relation = match fact {
            AtomicFact::MultivariableAnalysisFact(f) => Some(&f.relation),
            AtomicFact::NotMultivariableAnalysisFact(f) => Some(&f.relation),
            _ => None,
        };
        if let Some(relation) = multi_relation {
            let Some((function_domain, requirements)) =
                self.multivariable_domain_requirements(relation, verify_state)?
            else {
                return Ok(VerifyAtomicFactWellDefinedResult::Failed(
                    FailToVerifyAtomicFactWellDefinedResult::RealAnalysisDomain {
                        fact: fact.clone(),
                        well_defined_of_each_parameter: succeeded_args,
                    },
                ));
            };
            let mut completed = Vec::new();
            for (index, requirement) in requirements.into_iter().enumerate() {
                let proof = match self.verify_requirement_with_checked_arguments(
                    &requirement,
                    &args,
                    index,
                    verify_state,
                )? {
                    Ok(proof) => proof,
                    Err(result) => {
                        return Ok(VerifyAtomicFactWellDefinedResult::Failed(
                            FailToVerifyAtomicFactWellDefinedResult::Domain {
                                fact: fact.clone(),
                                well_defined_of_each_parameter: succeeded_args,
                                predicate_signature,
                                completed,
                                requirement,
                                result: Box::new(result),
                            },
                        ));
                    }
                };
                completed.push(proof);
            }
            return Ok(VerifyAtomicFactWellDefinedResult::Success(
                AtomicFactWellDefinedProof::new(self.result_detail(), || {
                    DetailedAtomicFactWellDefinedProof {
                        well_defined_of_each_parameter: succeeded_args,
                        predicate_signature,
                        predicate_domain: PredicateDomainProof::MultivariableAnalysis(
                            super::well_defined_result::MultivariableAnalysisPredicateDomainProof {
                                function_domain: Box::new(function_domain),
                                requirements: completed,
                            },
                        ),
                    }
                })?,
            ));
        }
        let analysis_sequence = match fact {
            AtomicFact::SequenceAnalysisFact(f) => Some(&f.sequence),
            AtomicFact::NotSequenceAnalysisFact(f) => Some(&f.sequence),
            _ => None,
        };
        if let Some(sequence) = analysis_sequence {
            let Some(sequence_source) =
                self.checked_real_sequence_domain(sequence, verify_state)?
            else {
                return Ok(VerifyAtomicFactWellDefinedResult::Failed(
                    FailToVerifyAtomicFactWellDefinedResult::RealAnalysisDomain {
                        fact: fact.clone(),
                        well_defined_of_each_parameter: succeeded_args,
                    },
                ));
            };
            return Ok(VerifyAtomicFactWellDefinedResult::Success(
                AtomicFactWellDefinedProof::new(self.result_detail(), || {
                    DetailedAtomicFactWellDefinedProof {
                        well_defined_of_each_parameter: succeeded_args,
                        predicate_signature,
                        predicate_domain: PredicateDomainProof::SequenceAnalysis(
                            super::well_defined_result::SequenceAnalysisPredicateDomainProof {
                                sequence_source: Box::new(sequence_source),
                            },
                        ),
                    }
                })?,
            ));
        }
        let analysis_function = match fact {
            AtomicFact::NormalAtomicFact(f)
                if f.predicate
                    == crate::ast::names::AtomicName::plain("is_darboux_enclosure".into()) =>
            {
                Some(&f.body[0])
            }
            AtomicFact::NotNormalAtomicFact(f)
                if f.predicate
                    == crate::ast::names::AtomicName::plain("is_darboux_enclosure".into()) =>
            {
                Some(&f.body[0])
            }
            AtomicFact::HasRiemannIntegralFact(f) => Some(&f.function),
            AtomicFact::NotHasRiemannIntegralFact(f) => Some(&f.function),
            AtomicFact::FunctionRiemannIntegrableFact(f) => Some(&f.function),
            AtomicFact::NotFunctionRiemannIntegrableFact(f) => Some(&f.function),
            AtomicFact::HasDerivativeAtFact(f) => Some(&f.function),
            AtomicFact::NotHasDerivativeAtFact(f) => Some(&f.function),
            AtomicFact::FunctionDifferentiableAtFact(f) => Some(&f.function),
            AtomicFact::NotFunctionDifferentiableAtFact(f) => Some(&f.function),
            AtomicFact::FunctionContinuousAtFact(f) => Some(&f.function),
            AtomicFact::NotFunctionContinuousAtFact(f) => Some(&f.function),
            AtomicFact::FunctionContinuousFact(f) => Some(&f.function),
            AtomicFact::NotFunctionContinuousFact(f) => Some(&f.function),
            AtomicFact::FunctionLipschitzFact(f) => Some(&f.function),
            AtomicFact::NotFunctionLipschitzFact(f) => Some(&f.function),
            _ => None,
        };
        if let Some(function) = analysis_function {
            let Some(function_domain) =
                self.checked_real_function_limit_domain(function, verify_state)?
            else {
                return Ok(VerifyAtomicFactWellDefinedResult::Failed(
                    FailToVerifyAtomicFactWellDefinedResult::RealAnalysisDomain {
                        fact: fact.clone(),
                        well_defined_of_each_parameter: succeeded_args,
                    },
                ));
            };
            let mut requirements = match fact {
                AtomicFact::NormalAtomicFact(f)
                    if f.predicate
                        == crate::ast::names::AtomicName::plain("is_darboux_enclosure".into()) =>
                {
                    let mut req = self.riemann_domain_requirements(
                        f.body[1].clone(),
                        f.body[2].clone(),
                        function_domain.domain.clone(),
                    );
                    req.extend(self.riemann_enclosure_signature_requirements(&f.body));
                    req
                }
                AtomicFact::NotNormalAtomicFact(f)
                    if f.predicate
                        == crate::ast::names::AtomicName::plain("is_darboux_enclosure".into()) =>
                {
                    let mut req = self.riemann_domain_requirements(
                        f.body[1].clone(),
                        f.body[2].clone(),
                        function_domain.domain.clone(),
                    );
                    req.extend(self.riemann_enclosure_signature_requirements(&f.body));
                    req
                }
                AtomicFact::HasRiemannIntegralFact(f) => self.riemann_domain_requirements(
                    f.lower.clone(),
                    f.upper.clone(),
                    function_domain.domain.clone(),
                ),
                AtomicFact::NotHasRiemannIntegralFact(f) => self.riemann_domain_requirements(
                    f.lower.clone(),
                    f.upper.clone(),
                    function_domain.domain.clone(),
                ),
                AtomicFact::FunctionRiemannIntegrableFact(f) => self.riemann_domain_requirements(
                    f.lower.clone(),
                    f.upper.clone(),
                    function_domain.domain.clone(),
                ),
                AtomicFact::NotFunctionRiemannIntegrableFact(f) => self
                    .riemann_domain_requirements(
                        f.lower.clone(),
                        f.upper.clone(),
                        function_domain.domain.clone(),
                    ),
                _ => Vec::new(),
            };
            let point = match fact {
                AtomicFact::HasDerivativeAtFact(f) => Some(&f.point),
                AtomicFact::NotHasDerivativeAtFact(f) => Some(&f.point),
                AtomicFact::FunctionDifferentiableAtFact(f) => Some(&f.point),
                AtomicFact::NotFunctionDifferentiableAtFact(f) => Some(&f.point),
                AtomicFact::FunctionContinuousAtFact(f) => Some(&f.point),
                AtomicFact::NotFunctionContinuousAtFact(f) => Some(&f.point),
                _ => None,
            };
            if let Some(point) = point {
                requirements.push(crate::ast::fact::Fact::from(crate::ast::fact::InFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    element: point.clone(),
                    set: function_domain.domain.clone(),
                    line_file: None,
                }));
            }
            let derivative_value = match fact {
                AtomicFact::HasRiemannIntegralFact(f) => Some(&f.value),
                AtomicFact::NotHasRiemannIntegralFact(f) => Some(&f.value),
                AtomicFact::HasDerivativeAtFact(f) => Some(&f.value),
                AtomicFact::NotHasDerivativeAtFact(f) => Some(&f.value),
                _ => None,
            };
            if let Some(value) = derivative_value {
                requirements.push(
                    crate::ast::fact::InFact {
                        fact_id: self.global_ids.allocate_fact_id(),
                        element: value.clone(),
                        set: Obj::StandardSet(crate::ast::obj::StandardSet::R),
                        line_file: None,
                    }
                    .into(),
                );
            }
            let constant = match fact {
                AtomicFact::FunctionLipschitzFact(f) => Some(&f.constant),
                AtomicFact::NotFunctionLipschitzFact(f) => Some(&f.constant),
                _ => None,
            };
            if let Some(constant) = constant {
                requirements.push(crate::ast::fact::Fact::from(crate::ast::fact::InFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    element: constant.clone(),
                    set: Obj::StandardSet(crate::ast::obj::StandardSet::R),
                    line_file: None,
                }));
                requirements.push(crate::ast::fact::Fact::from(
                    crate::ast::fact::GreaterEqualFact {
                        fact_id: self.global_ids.allocate_fact_id(),
                        left: constant.clone(),
                        right: Obj::Literal(crate::ast::obj::Literal::Number(
                            crate::ast::obj::Number {
                                normalized_value: "0".into(),
                            },
                        )),
                        line_file: None,
                    },
                ));
            }
            let mut completed = Vec::new();
            for (index, requirement) in requirements.into_iter().enumerate() {
                let proof = match self.verify_requirement_with_checked_arguments(
                    &requirement,
                    &args,
                    index,
                    verify_state.capped_at(
                        crate::execute::execute_fact_stmt::VerifyStateLevel::BuiltinRule,
                    ),
                )? {
                    Ok(proof) => proof,
                    Err(result) => {
                        return Ok(VerifyAtomicFactWellDefinedResult::Failed(
                            FailToVerifyAtomicFactWellDefinedResult::Domain {
                                fact: fact.clone(),
                                well_defined_of_each_parameter: succeeded_args,
                                predicate_signature,
                                completed,
                                requirement,
                                result: Box::new(result),
                            },
                        ));
                    }
                };
                completed.push(proof);
            }
            return Ok(VerifyAtomicFactWellDefinedResult::Success(
                AtomicFactWellDefinedProof::new(self.result_detail(), || {
                    DetailedAtomicFactWellDefinedProof {
                        well_defined_of_each_parameter: succeeded_args,
                        predicate_signature,
                        predicate_domain: PredicateDomainProof::FunctionAnalysis(
                            super::well_defined_result::FunctionAnalysisPredicateDomainProof {
                                function_domain,
                                requirements: completed,
                            },
                        ),
                    }
                })?,
            ));
        }
        let function_limit = match fact {
            AtomicFact::HasFunctionLimitFact(f) => Some((&f.function, &f.approach, &f.value)),
            AtomicFact::NotHasFunctionLimitFact(f) => Some((&f.function, &f.approach, &f.value)),
            _ => None,
        };
        if let Some((function, approach, value)) = function_limit {
            let Some(function_domain) =
                self.checked_real_function_limit_domain(function, verify_state)?
            else {
                return Ok(VerifyAtomicFactWellDefinedResult::Failed(
                    FailToVerifyAtomicFactWellDefinedResult::FunctionLimitDomain {
                        fact: fact.clone(),
                        function: function.clone(),
                        well_defined_of_each_parameter: succeeded_args,
                    },
                ));
            };
            let mut real_proofs = Vec::new();
            for element in approach.point().into_iter().chain(std::iter::once(value)) {
                let requirement = self.function_limit_real_member(element.clone());
                let result = self.verify_fact(&requirement, verify_state)?;
                if result.is_failed() {
                    return Ok(VerifyAtomicFactWellDefinedResult::Failed(
                        FailToVerifyAtomicFactWellDefinedResult::Domain {
                            fact: fact.clone(),
                            well_defined_of_each_parameter: succeeded_args,
                            predicate_signature,
                            completed: Vec::new(),
                            requirement,
                            result: Box::new(result),
                        },
                    ));
                }
                real_proofs.push(Box::new(result));
            }
            let value_real = real_proofs.pop().unwrap();
            let approach_real = match approach {
                LimitApproach::AtPositiveInfinity => {
                    FunctionLimitApproachRealProof::AtPositiveInfinity
                }
                LimitApproach::AtNegativeInfinity => {
                    FunctionLimitApproachRealProof::AtNegativeInfinity
                }
                _ => FunctionLimitApproachRealProof::Finite(
                    real_proofs.pop().expect("finite point evidence"),
                ),
            };
            return Ok(VerifyAtomicFactWellDefinedResult::Success(
                AtomicFactWellDefinedProof::new(self.result_detail(), || {
                    DetailedAtomicFactWellDefinedProof {
                        well_defined_of_each_parameter: succeeded_args,
                        predicate_signature,
                        predicate_domain: PredicateDomainProof::FunctionLimit(
                            super::well_defined_result::FunctionLimitPredicateDomainProof {
                                function_domain,
                                approach_real,
                                value_real,
                            },
                        ),
                    }
                })?,
            ));
        }
        // The new limit family consumes the checked callable argument's exact
        // signature; it does not rerun its body under the predicate-domain ceiling.
        let sequence_limit = match fact {
            AtomicFact::HasSequenceLimitFact(f) => Some((&f.sequence, &f.value)),
            AtomicFact::HasSequenceLimsupFact(f) => Some((&f.sequence, &f.value)),
            AtomicFact::HasSequenceLiminfFact(f) => Some((&f.sequence, &f.value)),
            AtomicFact::NotHasSequenceLimitFact(f) => Some((&f.sequence, &f.value)),
            AtomicFact::NotHasSequenceLimsupFact(f) => Some((&f.sequence, &f.value)),
            AtomicFact::NotHasSequenceLiminfFact(f) => Some((&f.sequence, &f.value)),
            _ => None,
        };
        if let Some((sequence, value)) = sequence_limit {
            if let Some(sequence_source) =
                self.checked_real_sequence_domain(sequence, verify_state)?
            {
                if let Some(value_real) = self.search_membership_of_checked_object(
                    value,
                    &crate::ast::obj::StandardSet::R,
                    verify_state,
                ) {
                    return Ok(VerifyAtomicFactWellDefinedResult::Success(
                        AtomicFactWellDefinedProof::new(self.result_detail(), || {
                            DetailedAtomicFactWellDefinedProof {
                                well_defined_of_each_parameter: succeeded_args,
                                predicate_signature,
                                predicate_domain: PredicateDomainProof::SequenceLimit(
                                    super::well_defined_result::SequenceLimitPredicateDomainProof {
                                        sequence_source: Box::new(sequence_source),
                                        value_real,
                                    },
                                ),
                            }
                        })?,
                    ));
                }
            }
        }
        // A stored well-defined a%d=0 has exactly Dvd's integer/nonzero
        // domain. Reuse that checked source, including at a reduced ceiling.
        let divisibility_args = match fact {
            AtomicFact::DvdFact(f) => Some((&f.left, &f.right)),
            AtomicFact::NotDvdFact(f) => Some((&f.left, &f.right)),
            _ => None,
        };
        if let Some((dividend, divisor)) = divisibility_args {
            if let Some(source) = self.lookup_known_zero_remainder(dividend, divisor) {
                return Ok(VerifyAtomicFactWellDefinedResult::Success(
                    AtomicFactWellDefinedProof::new(self.result_detail(), || {
                        DetailedAtomicFactWellDefinedProof {
                            well_defined_of_each_parameter: succeeded_args,
                            predicate_signature,
                            predicate_domain: PredicateDomainProof::ByKnownZeroRemainder(Box::new(
                                source,
                            )),
                        }
                    })?,
                ));
            }
        }
        let mut first_failure = None;
        let routes = if let Some(arguments) = super::super::antiderivative::arguments(fact) {
            let Some(requirements) =
                super::super::antiderivative::domain_requirements(self, arguments, verify_state)?
            else {
                return Ok(VerifyAtomicFactWellDefinedResult::Failed(
                    FailToVerifyAtomicFactWellDefinedResult::RealAnalysisDomain {
                        fact: fact.clone(),
                        well_defined_of_each_parameter: succeeded_args,
                    },
                ));
            };
            vec![requirements]
        } else {
            self.atomic_predicate_domain_requirement_routes(fact)
        };
        for requirements in routes {
            let mut predicate_domain = Vec::new();
            let mut failed = None;
            for (index, requirement) in requirements.iter().enumerate() {
                match self.verify_requirement_with_checked_arguments(
                    requirement,
                    &args,
                    index,
                    verify_state.capped_at(
                        crate::execute::execute_fact_stmt::VerifyStateLevel::BuiltinRule,
                    ),
                )? {
                    Ok(proof) => {
                        if self.result_detail() == crate::result_detail::OutputDetail::Detailed {
                            predicate_domain.push(proof);
                        }
                    }
                    Err(result) => {
                        failed = Some((requirement.clone(), result));
                        break;
                    }
                }
            }
            if let Some((requirement, result)) = failed {
                if first_failure.is_none() {
                    first_failure = Some((predicate_domain, requirement, result));
                }
                continue;
            }
            return Ok(VerifyAtomicFactWellDefinedResult::Success(
                AtomicFactWellDefinedProof::new(self.result_detail(), || {
                    DetailedAtomicFactWellDefinedProof {
                        well_defined_of_each_parameter: succeeded_args,
                        predicate_signature,
                        predicate_domain: PredicateDomainProof::ByRequirements(predicate_domain),
                    }
                })?,
            ));
        }
        let (completed, requirement, result) =
            first_failure.expect("one domain route is always present");
        Ok(VerifyAtomicFactWellDefinedResult::Failed(
            FailToVerifyAtomicFactWellDefinedResult::Domain {
                fact: fact.clone(),
                well_defined_of_each_parameter: succeeded_args,
                predicate_signature,
                completed,
                requirement,
                result: Box::new(result),
            },
        ))
    }

    // For and/chain mixed storage: EqualFact uses equality WD then converts;
    // other atomics use atomic-except-equality WD.
    pub(crate) fn verify_atomic_component_well_definedness(
        &mut self,
        atomic: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyAtomicFactWellDefinedResult> {
        match atomic {
            AtomicFact::EqualFact(equal_fact) => {
                match self.verify_equal_fact_well_definedness(equal_fact, verify_state)? {
                    VerifyEqualFactWellDefinedResult::Success(proof) => {
                        Ok(VerifyAtomicFactWellDefinedResult::Success(proof.into()))
                    }
                    VerifyEqualFactWellDefinedResult::Failed(reason) => {
                        Ok(VerifyAtomicFactWellDefinedResult::Failed(reason.into()))
                    }
                }
            }
            _ => self.verify_atomic_fact_well_definedness(atomic, verify_state),
        }
    }
}

impl Runtime {
    // Each callable contract retains its actual signature and checked carrier
    // equalities. Choice has two independent callable obligations; neither may
    // be discarded when trying an equivalent spelling for the other.
    fn atomic_predicate_domain_requirement_routes(
        &mut self,
        fact: &AtomicFact,
    ) -> Vec<Vec<crate::ast::fact::Fact>> {
        use crate::ast::obj::{FamilyUnion, SetOperator};
        let primary = self.atomic_predicate_domain_requirements(fact);
        let divisibility_args = match fact {
            AtomicFact::DvdFact(f) => Some((&f.left, &f.right)),
            AtomicFact::NotDvdFact(f) => Some((&f.left, &f.right)),
            _ => None,
        };
        if let Some((dividend, divisor)) = divisibility_args {
            use crate::ast::fact::{Fact, InFact, NotEqualFact};
            use crate::ast::obj::{Literal, Number, StandardSet};
            let mut expanded = Vec::new();
            for element in [dividend, divisor] {
                expanded.push(Fact::from(InFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    element: element.clone(),
                    set: Obj::StandardSet(StandardSet::Z),
                    line_file: None,
                }));
            }
            expanded.push(Fact::from(NotEqualFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left: divisor.clone(),
                right: Obj::Literal(Literal::Number(Number::new("0".into()))),
                line_file: None,
            }));
            return vec![primary, expanded];
        }
        if let Some((domain, codomain, function)) = function_property_signature_args(fact) {
            return self
                .callable_signature_requirement_routes(domain, codomain, function)
                .into_iter()
                .map(|route| primary[..2].iter().cloned().chain(route).collect())
                .collect();
        }
        let choice = match fact {
            AtomicFact::IsChoiceFunctionForFact(f) => {
                Some((&f.index, &f.set, &f.family, &f.choice))
            }
            AtomicFact::NotIsChoiceFunctionForFact(f) => {
                Some((&f.index, &f.set, &f.family, &f.choice))
            }
            _ => None,
        };
        if let Some((index, set, family, choice)) = choice {
            let union = Obj::SetOperator(SetOperator::FamilyUnion(FamilyUnion {
                left: Box::new(set.clone()),
            }));
            let families = self.callable_signature_requirement_routes(index, set, family);
            let choices = self.callable_signature_requirement_routes(index, &union, choice);
            let mut routes = Vec::new();
            for family_route in families {
                for choice_route in &choices {
                    routes.push(
                        primary[..2]
                            .iter()
                            .cloned()
                            .chain(family_route.iter().cloned())
                            .chain(choice_route.iter().cloned())
                            .collect(),
                    );
                }
            }
            return routes;
        }
        vec![primary]
    }

    // Legacy accepts equal carriers and the exact N+ prefix `k <= n` on
    // closed_range(1,n). Every alternative checks the actual callable type and
    // all equalities; a property assumption is never its own type evidence.
    fn callable_signature_requirement_routes(
        &mut self,
        domain: &Obj,
        codomain: &Obj,
        function: &Obj,
    ) -> Vec<Vec<crate::ast::fact::Fact>> {
        use crate::ast::fact::{EqualFact, Fact, InFact, QuantifierFreeFact};
        use crate::ast::obj::{
            FunctionSpace, IdentifierObj, Literal, Number, SetFormer, StandardSet,
        };
        let signature = self.predicate_unary_fn_set(domain, codomain);
        let mut routes = vec![vec![Fact::AtomicFact(AtomicFact::InFact(InFact {
            fact_id: self.global_ids.allocate_fact_id(),
            element: function.clone(),
            set: signature,
            line_file: None,
        }))]];
        let mut signatures: Vec<_> = self
            .collect_in_function_set_candidates(function)
            .into_iter()
            .map(|(signature, _)| signature)
            .collect();
        if let Obj::FunctionSpace(FunctionSpace::AnonymousFn(value)) = function {
            signatures.push(value.body.clone());
        }
        for signature in signatures {
            let [group] = signature.set_bound_parameters.groups.as_slice() else {
                continue;
            };
            let [param] = group.params.as_slice() else {
                continue;
            };
            let carrier_pairs = if signature.dom_facts.is_empty() {
                vec![(group.param_type.as_ref().clone(), domain.clone())]
            } else {
                let Obj::SetFormer(SetFormer::ClosedRange(range)) = domain else {
                    continue;
                };
                if !matches!(
                    group.param_type.as_ref(),
                    Obj::StandardSet(StandardSet::NPos)
                ) {
                    continue;
                }
                let [QuantifierFreeFact::AtomicFact(AtomicFact::LessEqualFact(bound))] =
                    signature.dom_facts.as_slice()
                else {
                    continue;
                };
                if bound.left != Obj::Identifier(IdentifierObj::from_bound_name(param)) {
                    continue;
                }
                vec![
                    (
                        range.start.as_ref().clone(),
                        Obj::Literal(Literal::Number(Number {
                            normalized_value: "1".to_string(),
                        })),
                    ),
                    (range.end.as_ref().clone(), bound.right.clone()),
                ]
            };
            let return_set = signature.ret_set.as_ref().clone();
            let mut requirements = vec![Fact::AtomicFact(AtomicFact::InFact(InFact {
                fact_id: self.global_ids.allocate_fact_id(),
                element: function.clone(),
                set: Obj::FunctionSpace(FunctionSpace::FnSet(signature)),
                line_file: None,
            }))];
            for (left, right) in carrier_pairs
                .into_iter()
                .chain([(return_set, codomain.clone())])
            {
                requirements.push(Fact::AtomicFact(AtomicFact::EqualFact(EqualFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    left,
                    right,
                    line_file: None,
                })));
            }
            routes.push(requirements);
        }
        routes
    }

    // Partial numeric predicates require their declared carriers before they
    // can enter an assumption or a proof search. Both polarities share a domain.
    fn atomic_predicate_domain_requirements(
        &mut self,
        fact: &AtomicFact,
    ) -> Vec<crate::ast::fact::Fact> {
        use crate::ast::fact::{Fact, InFact, IsSetFact};
        use crate::ast::obj::StandardSet;
        use crate::ast::obj::{FamilyUnion, SetOperator};
        use StandardSet::{ZStar, N, R, Z};
        let analysis = match fact {
            AtomicFact::RealSetBoundFact(f) => Some(vec![
                crate::ast::fact::Fact::from(crate::ast::fact::SubsetFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    left: f.set.clone(),
                    right: Obj::StandardSet(R),
                    line_file: None,
                }),
                crate::ast::fact::Fact::from(InFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    element: f.bound.clone(),
                    set: Obj::StandardSet(R),
                    line_file: None,
                }),
            ]),
            AtomicFact::NotRealSetBoundFact(f) => Some(vec![
                crate::ast::fact::Fact::from(crate::ast::fact::SubsetFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    left: f.set.clone(),
                    right: Obj::StandardSet(R),
                    line_file: None,
                }),
                crate::ast::fact::Fact::from(InFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    element: f.bound.clone(),
                    set: Obj::StandardSet(R),
                    line_file: None,
                }),
            ]),
            AtomicFact::RealSetBoundedFact(f) => Some(vec![crate::ast::fact::Fact::from(
                crate::ast::fact::SubsetFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    left: f.set.clone(),
                    right: Obj::StandardSet(R),
                    line_file: None,
                },
            )]),
            AtomicFact::NotRealSetBoundedFact(f) => Some(vec![crate::ast::fact::Fact::from(
                crate::ast::fact::SubsetFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    left: f.set.clone(),
                    right: Obj::StandardSet(R),
                    line_file: None,
                },
            )]),
            AtomicFact::RealAccumulationFact(f) => Some(vec![
                crate::ast::fact::Fact::from(crate::ast::fact::SubsetFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    left: f.domain.clone(),
                    right: Obj::StandardSet(R),
                    line_file: None,
                }),
                crate::ast::fact::Fact::from(InFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    element: f.point.clone(),
                    set: Obj::StandardSet(R),
                    line_file: None,
                }),
            ]),
            AtomicFact::NotRealAccumulationFact(f) => Some(vec![
                crate::ast::fact::Fact::from(crate::ast::fact::SubsetFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    left: f.domain.clone(),
                    right: Obj::StandardSet(R),
                    line_file: None,
                }),
                crate::ast::fact::Fact::from(InFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    element: f.point.clone(),
                    set: Obj::StandardSet(R),
                    line_file: None,
                }),
            ]),
            _ => None,
        };
        if let Some(requirements) = analysis {
            return requirements;
        }
        let sequence_limit = match fact {
            AtomicFact::HasSequenceLimitFact(f) => Some((&f.sequence, &f.value)),
            AtomicFact::HasSequenceLimsupFact(f) => Some((&f.sequence, &f.value)),
            AtomicFact::HasSequenceLiminfFact(f) => Some((&f.sequence, &f.value)),
            AtomicFact::NotHasSequenceLimitFact(f) => Some((&f.sequence, &f.value)),
            AtomicFact::NotHasSequenceLimsupFact(f) => Some((&f.sequence, &f.value)),
            AtomicFact::NotHasSequenceLiminfFact(f) => Some((&f.sequence, &f.value)),
            _ => None,
        };
        if let Some((sequence, value)) = sequence_limit {
            return vec![
                crate::execute::execute_fact_stmt::sequence_limit::sequence_membership(
                    self,
                    sequence.clone(),
                ),
                crate::ast::fact::InFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    element: value.clone(),
                    set: Obj::StandardSet(StandardSet::R),
                    line_file: None,
                }
                .into(),
            ];
        }

        let function_property = function_property_signature_args(fact);
        if let Some((domain, codomain, function)) = function_property {
            let signature = self.predicate_unary_fn_set(domain, codomain);
            return vec![
                Fact::AtomicFact(AtomicFact::IsSetFact(IsSetFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    set: domain.clone(),
                    line_file: None,
                })),
                Fact::AtomicFact(AtomicFact::IsSetFact(IsSetFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    set: codomain.clone(),
                    line_file: None,
                })),
                Fact::AtomicFact(AtomicFact::InFact(InFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    element: function.clone(),
                    set: signature,
                    line_file: None,
                })),
            ];
        }
        let choice = match fact {
            AtomicFact::IsChoiceFunctionForFact(f) => {
                Some((&f.index, &f.set, &f.family, &f.choice))
            }
            AtomicFact::NotIsChoiceFunctionForFact(f) => {
                Some((&f.index, &f.set, &f.family, &f.choice))
            }
            _ => None,
        };
        if let Some((index, set, family, choice)) = choice {
            let family_signature = self.predicate_unary_fn_set(index, set);
            let union = Obj::SetOperator(SetOperator::FamilyUnion(FamilyUnion {
                left: Box::new(set.clone()),
            }));
            let choice_signature = self.predicate_unary_fn_set(index, &union);
            return vec![
                Fact::AtomicFact(AtomicFact::IsSetFact(IsSetFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    set: index.clone(),
                    line_file: None,
                })),
                Fact::AtomicFact(AtomicFact::IsSetFact(IsSetFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    set: set.clone(),
                    line_file: None,
                })),
                Fact::AtomicFact(AtomicFact::InFact(InFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    element: family.clone(),
                    set: family_signature,
                    line_file: None,
                })),
                Fact::AtomicFact(AtomicFact::InFact(InFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    element: choice.clone(),
                    set: choice_signature,
                    line_file: None,
                })),
            ];
        }
        let carriers = match fact {
            AtomicFact::PrimeFact(_) | AtomicFact::NotPrimeFact(_) => vec![N],
            AtomicFact::CoprimeFact(_) | AtomicFact::NotCoprimeFact(_) => vec![N, N],
            AtomicFact::DvdFact(_) | AtomicFact::NotDvdFact(_) => vec![Z, ZStar],
            AtomicFact::LessFact(_)
            | AtomicFact::NotLessFact(_)
            | AtomicFact::GreaterFact(_)
            | AtomicFact::NotGreaterFact(_)
            | AtomicFact::LessEqualFact(_)
            | AtomicFact::NotLessEqualFact(_)
            | AtomicFact::GreaterEqualFact(_)
            | AtomicFact::NotGreaterEqualFact(_) => vec![R, R],
            _ => return Vec::new(),
        };
        atomic_except_equality_fact_arg_objs(fact)
            .into_iter()
            .zip(carriers)
            .map(|(element, set)| {
                crate::ast::fact::Fact::AtomicFact(AtomicFact::InFact(crate::ast::fact::InFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    element: element.clone(),
                    set: Obj::StandardSet(set),
                    line_file: None,
                }))
            })
            .collect()
    }

    fn predicate_unary_fn_set(&mut self, domain: &Obj, codomain: &Obj) -> Obj {
        use crate::ast::obj::{FnSet, FunctionSpace};
        use crate::ast::param::{SetBoundParameterGroup, SetBoundParameterList};
        Obj::FunctionSpace(FunctionSpace::FnSet(FnSet {
            set_bound_parameters: SetBoundParameterList {
                groups: vec![SetBoundParameterGroup {
                    params: vec![self.fresh_internal_param()],
                    param_type: Box::new(domain.clone()),
                }],
            },
            dom_facts: Vec::new(),
            ret_set: Box::new(codomain.clone()),
        }))
    }
}

fn atomic_except_equality_fact_arg_objs(fact: &AtomicFact) -> Vec<&Obj> {
    match fact {
        AtomicFact::MultivariableAnalysisFact(f) => f.relation.argument_refs(),
        AtomicFact::NotMultivariableAnalysisFact(f) => f.relation.argument_refs(),
        AtomicFact::HasRiemannIntegralFact(f) => vec![&f.function, &f.lower, &f.upper, &f.value],
        AtomicFact::NotHasRiemannIntegralFact(f) => vec![&f.function, &f.lower, &f.upper, &f.value],
        AtomicFact::FunctionRiemannIntegrableFact(f) => vec![&f.function, &f.lower, &f.upper],
        AtomicFact::NotFunctionRiemannIntegrableFact(f) => vec![&f.function, &f.lower, &f.upper],
        AtomicFact::HasDerivativeAtFact(f) => vec![&f.function, &f.point, &f.value],
        AtomicFact::NotHasDerivativeAtFact(f) => vec![&f.function, &f.point, &f.value],
        AtomicFact::FunctionDifferentiableAtFact(f) => vec![&f.function, &f.point],
        AtomicFact::NotFunctionDifferentiableAtFact(f) => vec![&f.function, &f.point],
        AtomicFact::RealSetBoundFact(f) => vec![&f.set, &f.bound],
        AtomicFact::NotRealSetBoundFact(f) => vec![&f.set, &f.bound],
        AtomicFact::RealSetBoundedFact(f) => vec![&f.set],
        AtomicFact::NotRealSetBoundedFact(f) => vec![&f.set],
        AtomicFact::SequenceAnalysisFact(f) => vec![&f.sequence],
        AtomicFact::NotSequenceAnalysisFact(f) => vec![&f.sequence],
        AtomicFact::RealAccumulationFact(f) => vec![&f.domain, &f.point],
        AtomicFact::NotRealAccumulationFact(f) => vec![&f.domain, &f.point],
        AtomicFact::FunctionContinuousAtFact(f) => vec![&f.function, &f.point],
        AtomicFact::NotFunctionContinuousAtFact(f) => vec![&f.function, &f.point],
        AtomicFact::FunctionContinuousFact(f) => vec![&f.function],
        AtomicFact::NotFunctionContinuousFact(f) => vec![&f.function],
        AtomicFact::FunctionLipschitzFact(f) => vec![&f.function, &f.constant],
        AtomicFact::NotFunctionLipschitzFact(f) => vec![&f.function, &f.constant],
        AtomicFact::EqualFact(_) => unreachable!("EqualFact rejected above"),
        AtomicFact::NotEqualFact(f) => vec![&f.left, &f.right],
        AtomicFact::InFact(f) => vec![&f.element, &f.set],
        AtomicFact::NotInFact(f) => vec![&f.element, &f.set],
        AtomicFact::LessFact(f) => vec![&f.left, &f.right],
        AtomicFact::NotLessFact(f) => vec![&f.left, &f.right],
        AtomicFact::GreaterFact(f) => vec![&f.left, &f.right],
        AtomicFact::NotGreaterFact(f) => vec![&f.left, &f.right],
        AtomicFact::LessEqualFact(f) => vec![&f.left, &f.right],
        AtomicFact::NotLessEqualFact(f) => vec![&f.left, &f.right],
        AtomicFact::GreaterEqualFact(f) => vec![&f.left, &f.right],
        AtomicFact::NotGreaterEqualFact(f) => vec![&f.left, &f.right],
        AtomicFact::IsSetFact(f) => vec![&f.set],
        AtomicFact::NotIsSetFact(f) => vec![&f.set],
        AtomicFact::IsNonemptySetFact(f) => vec![&f.set],
        AtomicFact::NotIsNonemptySetFact(f) => vec![&f.set],
        AtomicFact::IsFiniteSetFact(f) => vec![&f.set],
        AtomicFact::NotIsFiniteSetFact(f) => vec![&f.set],
        AtomicFact::SubsetFact(f) => vec![&f.left, &f.right],
        AtomicFact::NotSubsetFact(f) => vec![&f.left, &f.right],
        AtomicFact::SupersetFact(f) => vec![&f.left, &f.right],
        AtomicFact::NotSupersetFact(f) => vec![&f.left, &f.right],
        AtomicFact::NormalAtomicFact(f) => f.body.iter().collect(),
        AtomicFact::NotNormalAtomicFact(f) => f.body.iter().collect(),
        AtomicFact::ProperSubsetFact(f) => vec![&f.left, &f.right],
        AtomicFact::NotProperSubsetFact(f) => vec![&f.left, &f.right],
        AtomicFact::ProperSupersetFact(f) => vec![&f.left, &f.right],
        AtomicFact::NotProperSupersetFact(f) => vec![&f.left, &f.right],
        AtomicFact::PrimeFact(f) => vec![&f.value],
        AtomicFact::NotPrimeFact(f) => vec![&f.value],
        AtomicFact::CoprimeFact(f) => vec![&f.left, &f.right],
        AtomicFact::NotCoprimeFact(f) => vec![&f.left, &f.right],
        AtomicFact::HasSequenceLimitFact(f) => vec![&f.sequence, &f.value],
        AtomicFact::HasSequenceLimsupFact(f) => vec![&f.sequence, &f.value],
        AtomicFact::HasSequenceLiminfFact(f) => vec![&f.sequence, &f.value],
        AtomicFact::HasFunctionLimitFact(f) => f.approach.operand_refs(&f.function, &f.value),
        AtomicFact::NotHasSequenceLimitFact(f) => vec![&f.sequence, &f.value],
        AtomicFact::NotHasSequenceLimsupFact(f) => vec![&f.sequence, &f.value],
        AtomicFact::NotHasSequenceLiminfFact(f) => vec![&f.sequence, &f.value],
        AtomicFact::NotHasFunctionLimitFact(f) => f.approach.operand_refs(&f.function, &f.value),
        AtomicFact::DvdFact(f) => vec![&f.left, &f.right],
        AtomicFact::NotDvdFact(f) => vec![&f.left, &f.right],
        AtomicFact::InjectiveFact(f) => vec![&f.domain, &f.codomain, &f.function],
        AtomicFact::NotInjectiveFact(f) => vec![&f.domain, &f.codomain, &f.function],
        AtomicFact::SurjectiveFact(f) => vec![&f.domain, &f.codomain, &f.function],
        AtomicFact::NotSurjectiveFact(f) => vec![&f.domain, &f.codomain, &f.function],
        AtomicFact::BijectiveFact(f) => vec![&f.domain, &f.codomain, &f.function],
        AtomicFact::NotBijectiveFact(f) => vec![&f.domain, &f.codomain, &f.function],
        AtomicFact::IsChoiceFunctionForFact(f) => vec![&f.index, &f.set, &f.family, &f.choice],
        AtomicFact::NotIsChoiceFunctionForFact(f) => vec![&f.index, &f.set, &f.family, &f.choice],
    }
}

#[cfg(test)]
#[path = "../../../../tests/unit/execute/predicate_signature_wd/tests.rs"]
mod predicate_signature_tests;

#[cfg(test)]
#[path = "../../../../tests/unit/execute/predicate_domain_wd/tests.rs"]
mod predicate_domain_tests;

fn function_property_signature_args(fact: &AtomicFact) -> Option<(&Obj, &Obj, &Obj)> {
    match fact {
        AtomicFact::InjectiveFact(f) => Some((&f.domain, &f.codomain, &f.function)),
        AtomicFact::NotInjectiveFact(f) => Some((&f.domain, &f.codomain, &f.function)),
        AtomicFact::SurjectiveFact(f) => Some((&f.domain, &f.codomain, &f.function)),
        AtomicFact::NotSurjectiveFact(f) => Some((&f.domain, &f.codomain, &f.function)),
        AtomicFact::BijectiveFact(f) => Some((&f.domain, &f.codomain, &f.function)),
        AtomicFact::NotBijectiveFact(f) => Some((&f.domain, &f.codomain, &f.function)),
        _ => None,
    }
}
