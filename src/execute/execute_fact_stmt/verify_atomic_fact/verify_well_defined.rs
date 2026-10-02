use crate::ast::fact::AtomicFact;
use crate::ast::obj::Obj;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::VerifyEqualFactWellDefinedResult;
use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::{
    AtomicFactWellDefinedProof, FailToVerifyAtomicFactWellDefinedResult,
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
        for arg in args {
            match self.verify_obj_well_definedness(arg, verify_state.clone())? {
                VerifyObjWellDefinedResult::Failed { reason, .. } => {
                    return Ok(VerifyAtomicFactWellDefinedResult::Failed(
                        FailToVerifyAtomicFactWellDefinedResult::Argument(reason),
                    ));
                }
                VerifyObjWellDefinedResult::Success(proof) => succeeded_args.push(proof),
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
                let signature = if let Some(def) = self.def_prop_visible(predicate) {
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
                            well_defined_of_each_parameter: succeeded_args,
                            reason: PredicateSignatureWellDefinedFailure::Undefined {
                                predicate: predicate.clone(),
                            },
                        },
                    ));
                };
                let (PredicateSignatureWellDefinedProof::Prop { arity, .. }
                | PredicateSignatureWellDefinedProof::AbstractProp { arity, .. }) = &signature
                else {
                    unreachable!("resolved user predicate signature")
                };
                if *arity != actual_arity {
                    return Ok(VerifyAtomicFactWellDefinedResult::Failed(
                        FailToVerifyAtomicFactWellDefinedResult::Predicate {
                            well_defined_of_each_parameter: succeeded_args,
                            reason: PredicateSignatureWellDefinedFailure::Arity {
                                predicate: predicate.clone(),
                                expected: *arity,
                                actual: actual_arity,
                            },
                        },
                    ));
                }
                signature
            }
            _ => PredicateSignatureWellDefinedProof::Builtin,
        };
        let mut first_failure = None;
        for requirements in self.atomic_predicate_domain_requirement_routes(fact) {
            let mut predicate_domain = Vec::new();
            let mut failed = None;
            for requirement in requirements {
                // Domain checks may cite existing equality paths and use the
                // ordinary budgeted proof routes, but must not expand equality
                // peers. A peer can be an anonymous function: WD of its binder
                // infers an order fact whose domain would expand the same peer.
                let mut domain_state = verify_state.clone();
                domain_state.equality_class_search =
                    crate::execute::execute_fact_stmt::EqualityClassSearchMode::StoredPathsOnly;
                let mut result = self.verify_fact(&requirement, domain_state.clone())?;
                if result.is_failed() {
                    // Reuse completed WD and call only calculation/citation
                    // leaves with the caller's restricted state. Re-running
                    // strategy WD here would reset its recursion budget.
                    result = self.complete_predicate_domain_leaf(result, domain_state)?;
                }
                if result.is_failed() {
                    failed = Some((requirement, result));
                    break;
                }
                predicate_domain.push(
                    super::well_defined_result::PredicateDomainWellDefinedProof {
                        requirement,
                        result: Box::new(result),
                    },
                );
            }
            if let Some((requirement, result)) = failed {
                if first_failure.is_none() {
                    first_failure = Some((predicate_domain, requirement, result));
                }
                continue;
            }
            return Ok(VerifyAtomicFactWellDefinedResult::Success(
                AtomicFactWellDefinedProof {
                    well_defined_of_each_parameter: succeeded_args,
                    predicate_signature,
                    predicate_domain,
                },
            ));
        }
        let (completed, requirement, result) =
            first_failure.expect("one domain route is always present");
        Ok(VerifyAtomicFactWellDefinedResult::Failed(
            FailToVerifyAtomicFactWellDefinedResult::Domain {
                well_defined_of_each_parameter: succeeded_args,
                predicate_signature,
                completed,
                requirement,
                result: Box::new(result),
            },
        ))
    }

    fn complete_predicate_domain_leaf(
        &mut self,
        result: crate::execute::execute_fact_stmt::VerifyFactResult,
        state: VerifyState,
    ) -> RuntimeResult<crate::execute::execute_fact_stmt::VerifyFactResult> {
        use crate::execute::execute_fact_stmt::VerifyFactResult;
        use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::{
            VerifyAtomicExceptEqualityFactResult, VerifyAtomicExceptEqualityFactFailed,
            AtomicExceptEqualityFactSearchedProof, atomic_except_equality_fact_result_from_success,
            atomic_except_equality_fact_result_from_search_fail,
        };
        match result {
            VerifyFactResult::AtomicExceptEquality(result) => match *result {
                VerifyAtomicExceptEqualityFactResult::Failed(
                    VerifyAtomicExceptEqualityFactFailed::FailToSearchProof {
                        fact,
                        well_defined_proof,
                    },
                ) => {
                    match self.search_atomic_except_equality_fact_proof_by_builtin_rule(
                        &fact,
                        state.known_only_no_wd(),
                    )? {
                        Some(proof) => Ok(atomic_except_equality_fact_result_from_success(
                            &fact,
                            well_defined_proof,
                            AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(proof),
                        )),
                        None => Ok(atomic_except_equality_fact_result_from_search_fail(
                            &fact,
                            well_defined_proof,
                        )),
                    }
                }
                other => Ok(VerifyFactResult::AtomicExceptEquality(Box::new(other))),
            },
            other => Ok(other),
        }
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
    // Legacy function-property WD accepts equal carrier spellings and the
    // exact N+ prefix signature `fn(k N+: k <= n) B` on closed_range(1, n).
    // Each alternative proves the actual signature and every carrier equality;
    // a spelling match or the property assumption is never type evidence.
    fn atomic_predicate_domain_requirement_routes(
        &mut self,
        fact: &AtomicFact,
    ) -> Vec<Vec<crate::ast::fact::Fact>> {
        use crate::ast::fact::{EqualFact, Fact, InFact, QuantifierFreeFact};
        use crate::ast::obj::{
            FunctionSpace, IdentifierObj, Literal, Number, SetFormer, StandardSet,
        };
        let primary = self.atomic_predicate_domain_requirements(fact);
        let mut routes = vec![primary.clone()];
        let Some((domain, codomain, function)) = function_property_signature_args(fact) else {
            return routes;
        };
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
            let mut requirements = primary[..2].to_vec();
            let return_set = signature.ret_set.as_ref().clone();
            requirements.push(Fact::AtomicFact(AtomicFact::InFact(InFact {
                fact_id: self.global_ids.allocate_fact_id(),
                element: function.clone(),
                set: Obj::FunctionSpace(FunctionSpace::FnSet(signature)),
                line_file: None,
            })));
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
        AtomicFact::IsTupleFact(f) => vec![&f.set],
        AtomicFact::NotIsTupleFact(f) => vec![&f.set],
        AtomicFact::IsCartFact(f) => vec![&f.set],
        AtomicFact::NotIsCartFact(f) => vec![&f.set],
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
