use super::helper::verify_goal_fact;
use super::result::{
    ExecByStmtResult, ExecByThmStmtFailed, ExecByThmStmtResult, ExecByThmStmtSuccess,
    ExecReleaseThmStmtFailed, ExecReleaseThmStmtResult, ExecReleaseThmStmtSuccess,
    ResolvedTheoremCallee,
};
use crate::ast::fact::{
    atomic_fact_args_ref, atomic_fact_has_positive_polarity, AtomicFact, EqualFact, Fact,
    ForallFact,
};
use crate::ast::obj::Obj;
use crate::ast::stmt::{ByThmStmt, ReleaseThmStmt, TheoremCall, TheoremCallArguments};
use crate::runtime::runtime_ids::IdentifierId;
use crate::runtime::{Runtime, RuntimeResult};
use std::collections::HashMap;

pub fn exec_release_thm_stmt(
    runtime: &mut Runtime,
    stmt: &ReleaseThmStmt,
) -> RuntimeResult<ExecReleaseThmStmtResult> {
    let origin = super::TheoremInvocationOrigin::ReleaseThm(stmt.clone());
    let thm_name = stmt.call.name.local_name().to_string();
    let (prepared, callee) = match prepare_release_conclusions(runtime, &stmt.call)? {
        Ok(value) => value,
        Err(failed) => {
            return Ok(ExecReleaseThmStmtResult::Failed(
                ExecReleaseThmStmtFailed::Preparation(Box::new(
                    super::TheoremInvocationPreparationFailure::new(origin, failed),
                )),
            ))
        }
    };
    let (outcome, local_env) = runtime.run_in_local_env_and_take_env(|rt| {
        verify_prepared_theorem(rt, &thm_name, &prepared, &stmt.line_file)
    })?;
    let verified = match outcome {
        Ok(value) => value,
        Err(failed) => {
            return Ok(ExecReleaseThmStmtResult::Failed(
                ExecReleaseThmStmtFailed::Local(Box::new(
                    super::TheoremInvocationLocalFailure::new(
                        origin,
                        callee,
                        prepared,
                        super::TheoremInvocationLocalFailed::Invocation(failed),
                        local_env,
                    ),
                )),
            ))
        }
    };
    let mut stored = Vec::with_capacity(prepared.conclusions.len());
    let mut stored_wd = Vec::with_capacity(prepared.conclusions.len());
    for (index, conclusion) in prepared.conclusions.iter().enumerate() {
        // Same verify/store stages as store_goal_fact_with_wd; retain its actual
        // failed WD certificate rather than reducing it to a storage message.
        let result = runtime
            .verify_fact_well_definedness(conclusion, super::helper::proof_verify_state())?;
        let crate::execute::execute_fact_stmt::VerifyFactWellDefinedResult::Success(wd) = result
        else {
            return Ok(ExecReleaseThmStmtResult::Failed(
                ExecReleaseThmStmtFailed::Closing(Box::new(
                    super::TheoremInvocationClosingFailure::new(
                        origin,
                        callee,
                        prepared,
                        super::TheoremInvocationCheckedLocal::Release(verified),
                        local_env,
                        super::TheoremInvocationClosingFailed::Release {
                            stored_wd,
                            stored,
                            index,
                            result,
                        },
                    ),
                )),
            ));
        };
        let result = runtime.store_fact_and_infer(
            conclusion,
            crate::execute::execute_fact_stmt::VerifyState::top_level(),
        )?;
        stored_wd.push(wd);
        stored.push(result);
    }
    let super::VerifiedTheoremInvocation {
        type_checks,
        function_domain,
        premise_checks,
        theorem_derivation,
        conclusions_wd,
    } = verified;
    let (type_proofs, type_stores) = type_checks
        .into_iter()
        .map(|check| (check.proof, check.stored))
        .unzip();
    let (dom_proofs, dom_stores) = premise_checks
        .into_iter()
        .map(|check| (check.proof, check.stored))
        .unzip();
    Ok(ExecReleaseThmStmtResult::Success(
        ExecReleaseThmStmtSuccess {
            call: stmt.call.clone(),
            callee,
            builtin: prepared.builtin,
            type_proofs,
            type_stores,
            function_domain,
            dom_proofs,
            dom_stores,
            theorem_derivation,
            conclusions_wd,
            local_env,
            stored_wd,
            stored,
        },
    ))
}

pub fn exec_by_thm_stmt(
    runtime: &mut Runtime,
    stmt: &ByThmStmt,
) -> RuntimeResult<ExecByStmtResult> {
    let origin = super::TheoremInvocationOrigin::ByThm(stmt.clone());
    let thm_name = stmt.call.name.local_name().to_string();
    let (prepared, callee) = match prepare_release_conclusions(runtime, &stmt.call)? {
        Ok(value) => value,
        Err(failed) => {
            return Ok(ExecByStmtResult::Thm(ExecByThmStmtResult::Failed(
                ExecByThmStmtFailed::Preparation(Box::new(
                    super::TheoremInvocationPreparationFailure::new(origin, failed),
                )),
            )))
        }
    };
    let selected: Fact = stmt.selected_fact.clone().into();
    let (outcome, local_env) = runtime.run_in_local_env_and_take_env(|rt| {
        let verified = match verify_prepared_theorem(rt, &thm_name, &prepared, &stmt.line_file)? {
            Ok(value) => value,
            Err(failed) => return Ok(Err(super::TheoremInvocationLocalFailed::Invocation(failed))),
        };
        let mut direct_conclusions = Vec::new();
        let mut returned_conclusions = Vec::with_capacity(prepared.conclusions.len());
        for conclusion in &prepared.conclusions {
            let stored = rt.store_fact_and_infer(
                conclusion,
                crate::execute::execute_fact_stmt::VerifyState::top_level(),
            )?;
            // Only returned atoms and explicit package components are selectable.
            for (_, atomic) in stored.atomic_components() {
                direct_conclusions.push(atomic);
            }
            returned_conclusions.push(stored);
        }
        let Some(selected_proof) =
            verify_selected_theorem_conclusion(rt, &stmt.selected_fact, &direct_conclusions)?
        else {
            return Ok(Err(super::TheoremInvocationLocalFailed::Selection {
                verified,
                returned_conclusions,
                failure: super::TheoremSelectionFailed::NotReturned {
                    fact: selected.clone(),
                },
            }));
        };
        if selected_proof.is_failed() {
            return Ok(Err(super::TheoremInvocationLocalFailed::Selection {
                verified,
                returned_conclusions,
                failure: super::TheoremSelectionFailed::Selected {
                    fact: selected.clone(),
                    result: selected_proof,
                },
            }));
        }
        Ok(Ok(super::SelectedTheoremInvocationVerified::new(
            verified,
            returned_conclusions,
            selected_proof,
        )))
    })?;
    let checked = match outcome {
        Ok(value) => value,
        Err(failed) => {
            return Ok(ExecByStmtResult::Thm(ExecByThmStmtResult::Failed(
                ExecByThmStmtFailed::Local(Box::new(super::TheoremInvocationLocalFailure::new(
                    origin, callee, prepared, failed, local_env,
                ))),
            )))
        }
    };
    let result =
        runtime.verify_fact_well_definedness(&selected, super::helper::proof_verify_state())?;
    let crate::execute::execute_fact_stmt::VerifyFactWellDefinedResult::Success(selected_wd) =
        result
    else {
        return Ok(ExecByStmtResult::Thm(ExecByThmStmtResult::Failed(
            ExecByThmStmtFailed::Closing(Box::new(super::TheoremInvocationClosingFailure::new(
                origin,
                callee,
                prepared,
                super::TheoremInvocationCheckedLocal::ByThm(checked),
                local_env,
                super::TheoremInvocationClosingFailed::ByThm { result },
            ))),
        )));
    };
    let stored = runtime.store_fact_and_infer(
        &selected,
        crate::execute::execute_fact_stmt::VerifyState::top_level(),
    )?;
    let super::SelectedTheoremInvocationVerified {
        invocation,
        returned_conclusions,
        selected_proof,
    } = checked;
    let super::VerifiedTheoremInvocation {
        type_checks,
        function_domain,
        premise_checks,
        theorem_derivation,
        conclusions_wd,
    } = invocation;
    let (type_proofs, type_stores) = type_checks
        .into_iter()
        .map(|check| (check.proof, check.stored))
        .unzip();
    let (dom_proofs, dom_stores) = premise_checks
        .into_iter()
        .map(|check| (check.proof, check.stored))
        .unzip();
    Ok(ExecByStmtResult::Thm(ExecByThmStmtResult::Success(
        ExecByThmStmtSuccess {
            call: stmt.call.clone(),
            callee,
            builtin: prepared.builtin,
            type_proofs,
            type_stores,
            function_domain,
            dom_proofs,
            dom_stores,
            theorem_derivation,
            conclusions_wd,
            returned_conclusions,
            selected_proof,
            local_env,
            selected_wd,
            stored,
        },
    )))
}

fn verify_prepared_function_domain(
    runtime: &mut Runtime,
    theorem: &str,
    builtin: &Option<super::result::BuiltinThmApplication>,
) -> RuntimeResult<
    Result<Option<super::result::BuiltinFunctionDomainProof>, super::TheoremFunctionDomainFailure>,
> {
    let Some(application) = builtin else {
        return Ok(Ok(None));
    };
    use crate::builtin_theorem::BuiltinTheoremId;
    if application.theorem == BuiltinTheoremId::TupleEqualFromCoordinates {
        let target = match runtime
            .tuple_equality_domain(&application.arguments[0], &application.arguments[1])?
        {
            Ok(value) => value,
            Err(message) => {
                return Ok(Err(super::TheoremFunctionDomainFailure::new(
                    Vec::new(),
                    ExecReleaseThmStmtFailed::BuiltinShape {
                        theorem: application.theorem,
                        message,
                    },
                )))
            }
        };
        let left = match runtime.verify_complete_function_domain(
            &application.arguments[0],
            &target,
            super::helper::proof_verify_state(),
        )? {
            Ok(value) => value,
            Err(result) => {
                return Ok(Err(super::TheoremFunctionDomainFailure::new(
                    Vec::new(),
                    ExecReleaseThmStmtFailed::FunctionDomain {
                        theorem: theorem.to_string(),
                        result,
                    },
                )))
            }
        };
        let right = match runtime.verify_complete_function_domain(
            &application.arguments[1],
            &target,
            super::helper::proof_verify_state(),
        )? {
            Ok(value) => value,
            Err(result) => {
                return Ok(Err(super::TheoremFunctionDomainFailure::new(
                    vec![left],
                    ExecReleaseThmStmtFailed::FunctionDomain {
                        theorem: theorem.to_string(),
                        result,
                    },
                )))
            }
        };
        return Ok(Ok(Some(
            super::result::BuiltinFunctionDomainProof::TupleEquality { left, right },
        )));
    }
    if !matches!(
        application.theorem,
        BuiltinTheoremId::FunctionSetMember | BuiltinTheoremId::CartesianMemberFromCoordinates
    ) {
        return Ok(Ok(None));
    }
    let target = if application.theorem == BuiltinTheoremId::CartesianMemberFromCoordinates {
        runtime
            .cart_definition_for_set(&application.arguments[1])
            .map(|cart| runtime.cart_function_signature(&cart))
    } else {
        runtime.function_space_signature(&application.arguments[1])
    };
    let Some(target) = target else {
        return Ok(Err(super::TheoremFunctionDomainFailure::new(
            Vec::new(),
            ExecReleaseThmStmtFailed::BuiltinShape {
                theorem: application.theorem,
                message: "second argument must be a function or sequence set".to_string(),
            },
        )));
    };
    Ok(
        match runtime.verify_complete_function_domain(
            &application.arguments[0],
            &target,
            super::helper::proof_verify_state(),
        )? {
            Ok(proof) => Ok(Some(super::result::BuiltinFunctionDomainProof::Membership(
                proof,
            ))),
            Err(result) => Err(super::TheoremFunctionDomainFailure::new(
                Vec::new(),
                ExecReleaseThmStmtFailed::FunctionDomain {
                    theorem: theorem.to_string(),
                    result,
                },
            )),
        },
    )
}

pub(crate) struct PreparedRelease {
    pub(crate) builtin: Option<super::result::BuiltinThmApplication>,
    pub(crate) type_facts: Vec<Fact>,
    pub(crate) dom_facts: Vec<Fact>,
    pub(crate) conclusions: Vec<Fact>,
}

pub(crate) fn prepare_release_conclusions(
    runtime: &mut Runtime,
    call: &TheoremCall,
) -> RuntimeResult<Result<(PreparedRelease, ResolvedTheoremCallee), ExecReleaseThmStmtFailed>> {
    if let Some(prepared) = super::builtin_thm::prepare_builtin_thm(runtime, call)? {
        return Ok(prepared.map(|p| (p, ResolvedTheoremCallee::Builtin)));
    }
    if let Some(def_thm) = runtime.def_thm_visible(&call.name).cloned() {
        let thm_name = call.name.local_name();
        let prepared = match &def_thm.fact {
            Fact::ForallFact(forall) => prepare_forall_release(runtime, forall, &call.arguments),
            other => match &call.arguments {
                TheoremCallArguments::Bare => Ok(Ok(PreparedRelease {
                    builtin: None,
                    type_facts: Vec::new(),
                    dom_facts: Vec::new(),
                    conclusions: vec![other.clone()],
                })),
                TheoremCallArguments::Parenthesized(_) => Ok(Err(ExecReleaseThmStmtFailed::Shape(
                    format!("release thm `{thm_name}`: non-forall theorem must be called without arguments"),
                ))),
            },
        }?;
        return Ok(prepared.map(|p| (p, ResolvedTheoremCallee::UserTheorem(def_thm))));
    }

    if let Some(axiom) = runtime.axiom_visible(&call.name).cloned() {
        let prepared = prepare_forall_release(runtime, &axiom.forall_fact, &call.arguments)?;
        return Ok(prepared.map(|p| (p, ResolvedTheoremCallee::UserAxiom(axiom))));
    }

    Ok(Err(ExecReleaseThmStmtFailed::ThmNotFound(
        call.name.display_string(),
    )))
}

fn prepare_forall_release(
    runtime: &mut Runtime,
    forall: &ForallFact,
    arguments: &TheoremCallArguments,
) -> RuntimeResult<Result<PreparedRelease, ExecReleaseThmStmtFailed>> {
    let param_ids = forall.typed_parameters.ordered_param_ids();
    let args: &[Obj] = match arguments {
        TheoremCallArguments::Parenthesized(args) => args,
        TheoremCallArguments::Bare => {
            return Ok(Err(ExecReleaseThmStmtFailed::Shape(
                "release thm: forall theorem call requires parenthesized arguments".to_string(),
            )));
        }
    };
    if args.len() != param_ids.len() {
        return Ok(Err(ExecReleaseThmStmtFailed::Shape(format!(
            "release thm: expected {} argument(s), got {}",
            param_ids.len(),
            args.len()
        ))));
    }

    let mut subst: HashMap<IdentifierId, Obj> = HashMap::new();
    for (id, arg) in param_ids.into_iter().zip(args.iter()) {
        subst.insert(id, arg.clone());
    }

    let type_facts = match runtime.type_facts_for_typed_arguments(&forall.typed_parameters, args) {
        Ok(facts) => facts,
        Err(message) => return Ok(Err(ExecReleaseThmStmtFailed::Instantiate(message))),
    };

    let mut dom_facts = Vec::with_capacity(forall.dom_facts.len());
    for dom in &forall.dom_facts {
        match runtime.inst_fact(dom, &subst) {
            Ok(f) => dom_facts.push(f),
            Err(err) => {
                return Ok(Err(ExecReleaseThmStmtFailed::Instantiate(err.to_string())));
            }
        }
    }

    let mut conclusions = Vec::with_capacity(forall.then_facts.len());
    for then in &forall.then_facts {
        let then_fact: Fact = then.clone().into();
        match runtime.inst_fact(&then_fact, &subst) {
            Ok(f) => conclusions.push(f),
            Err(err) => {
                return Ok(Err(ExecReleaseThmStmtFailed::Instantiate(err.to_string())));
            }
        }
    }

    Ok(Ok(PreparedRelease {
        builtin: None,
        type_facts,
        dom_facts,
        conclusions,
    }))
}

fn verify_prepared_theorem(
    runtime: &mut Runtime,
    theorem: &str,
    prepared: &PreparedRelease,
    line: &crate::ast::line_file::SourceLine,
) -> RuntimeResult<Result<super::VerifiedTheoremInvocation, super::TheoremInvocationFailed>> {
    let mut type_checks = Vec::with_capacity(prepared.type_facts.len());
    for (index, fact) in prepared.type_facts.iter().enumerate() {
        let proof = verify_goal_fact(runtime, fact)?;
        if proof.is_failed() {
            return Ok(Err(super::TheoremInvocationFailed::Type {
                type_checks,
                failure: ExecReleaseThmStmtFailed::Type {
                    theorem: theorem.to_string(),
                    fact: fact.clone(),
                    index,
                    result: proof,
                },
            }));
        }
        let stored = runtime.store_fact_and_infer(
            fact,
            crate::execute::execute_fact_stmt::VerifyState::top_level(),
        )?;
        type_checks.push(super::TheoremRequirementChecked::new(proof, stored));
    }
    let function_domain =
        match verify_prepared_function_domain(runtime, theorem, &prepared.builtin)? {
            Ok(value) => value,
            Err(result) => {
                return Ok(Err(super::TheoremInvocationFailed::FunctionDomain {
                    type_checks,
                    result,
                }))
            }
        };
    let mut premise_checks = Vec::with_capacity(prepared.dom_facts.len());
    for (index, fact) in prepared.dom_facts.iter().enumerate() {
        let proof = verify_goal_fact(runtime, fact)?;
        if proof.is_failed() {
            return Ok(Err(super::TheoremInvocationFailed::Premise {
                type_checks,
                function_domain,
                premise_checks,
                failure: ExecReleaseThmStmtFailed::Dom {
                    theorem: theorem.to_string(),
                    fact: fact.clone(),
                    index,
                    result: proof,
                },
            }));
        }
        let stored = runtime.store_fact_and_infer(
            fact,
            crate::execute::execute_fact_stmt::VerifyState::top_level(),
        )?;
        premise_checks.push(super::TheoremRequirementChecked::new(proof, stored));
    }
    let theorem_derivation =
        match super::builtin_thm::derive_sequence_extrema_bounded::derive_sequence_extrema_bounded(
            runtime,
            &prepared.builtin,
            line,
        )? {
            Ok(value) => value,
            Err(failure) => {
                return Ok(Err(super::TheoremInvocationFailed::Derivation {
                    type_checks,
                    function_domain,
                    premise_checks,
                    failure,
                }))
            }
        };
    let mut conclusions_wd = Vec::with_capacity(prepared.conclusions.len());
    for (index, fact) in prepared.conclusions.iter().enumerate() {
        let result =
            runtime.verify_fact_well_definedness(fact, super::helper::proof_verify_state())?;
        match result {
            crate::execute::execute_fact_stmt::VerifyFactWellDefinedResult::Success(proof) => {
                conclusions_wd.push(proof)
            }
            failed => {
                return Ok(Err(super::TheoremInvocationFailed::ConclusionWd {
                    type_checks,
                    function_domain,
                    premise_checks,
                    theorem_derivation,
                    conclusions_wd,
                    failure: ExecReleaseThmStmtFailed::ConclusionWd {
                        theorem: theorem.to_string(),
                        fact: fact.clone(),
                        index,
                        result: failed,
                    },
                }))
            }
        }
    }
    Ok(Ok(super::VerifiedTheoremInvocation::new(
        type_checks,
        function_domain,
        premise_checks,
        theorem_derivation,
        conclusions_wd,
    )))
}

fn verify_selected_theorem_conclusion(
    runtime: &mut Runtime,
    selected: &AtomicFact,
    conclusions: &[AtomicFact],
) -> RuntimeResult<Option<crate::execute::execute_fact_stmt::VerifyFactResult>> {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::{
        EqualFactSearchedProof,
        EqualFactSearchedProofByEquivalenceClass,
    };
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_they_are_the_same::search_equal_fact_proof_by_they_are_the_same;
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::{
        equal_fact_result_from_success, equal_fact_result_from_wd_fail,
        KnownEqualityAlphaEndpointsProof,
    };
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::well_defined_result::VerifyEqualFactWellDefinedResult;
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::{
        atomic_except_equality_fact_result_from_success,
        atomic_except_equality_fact_result_from_wd_fail,
        AtomicExceptEqualityFactSearchProofByKnownAtomicFact,
        AtomicExceptEqualityFactSearchedProof,
    };
    use crate::execute::execute_fact_stmt::VerifyAtomicFactWellDefinedResult;

    let selected_args = atomic_fact_args_ref(selected);
    for conclusion in conclusions {
        if selected.prop_name() != conclusion.prop_name()
            || atomic_fact_has_positive_polarity(selected)
                != atomic_fact_has_positive_polarity(conclusion)
        {
            continue;
        }
        let conclusion_args = atomic_fact_args_ref(conclusion);
        if selected_args.len() != conclusion_args.len() {
            continue;
        }
        let mut identities = Vec::new();
        for (known, goal) in conclusion_args.iter().zip(&selected_args) {
            let comparison = EqualFact {
                fact_id: selected.fact_id(),
                left: (*known).clone(),
                right: (*goal).clone(),
                line_file: None,
            };
            let Some(identity) = search_equal_fact_proof_by_they_are_the_same(&comparison) else {
                break;
            };
            identities.push(identity);
        }
        if identities.len() != selected_args.len() {
            continue;
        }

        if let (AtomicFact::EqualFact(goal), AtomicFact::EqualFact(cited)) = (selected, conclusion)
        {
            let well_defined = match runtime
                .verify_equal_fact_well_definedness(goal, super::helper::proof_verify_state())?
            {
                VerifyEqualFactWellDefinedResult::Success(proof) => proof,
                VerifyEqualFactWellDefinedResult::Failed(reason) => {
                    return Ok(Some(equal_fact_result_from_wd_fail(reason)));
                }
            };
            let mut identities = identities.into_iter();
            let proof = KnownEqualityAlphaEndpointsProof {
                cited: cited.clone(),
                reversed: false,
                left_identity: identities.next().expect("equality left identity"),
                right_identity: identities.next().expect("equality right identity"),
            };
            return Ok(Some(equal_fact_result_from_success(
                goal,
                well_defined,
                EqualFactSearchedProof::ByEquivalenceClass(
                    EqualFactSearchedProofByEquivalenceClass::AlphaEndpoints(proof),
                ),
            )));
        }

        let well_defined = match runtime
            .verify_atomic_fact_well_definedness(selected, super::helper::proof_verify_state())?
        {
            VerifyAtomicFactWellDefinedResult::Success(proof) => proof,
            VerifyAtomicFactWellDefinedResult::Failed(reason) => {
                return Ok(Some(atomic_except_equality_fact_result_from_wd_fail(
                    reason,
                )));
            }
        };
        let proof = AtomicExceptEqualityFactSearchProofByKnownAtomicFact {
            cite_fact_id: conclusion.fact_id(),
            why_parameters_of_known_fact_are_equal_to_givens: identities
                .into_iter()
                .map(Into::into)
                .collect(),
        };
        return Ok(Some(atomic_except_equality_fact_result_from_success(
            selected,
            well_defined,
            AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(proof),
        )));
    }
    Ok(None)
}

#[cfg(test)]
#[path = "../../../tests/unit/execute/by_thm_selection/tests.rs"]
mod by_thm_selection_tests;
