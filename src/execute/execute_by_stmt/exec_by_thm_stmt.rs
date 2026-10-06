use super::helper::{store_goal_fact, verify_goal_fact};
use super::result::{
    ExecByStmtResult, ExecByThmStmtFailed, ExecByThmStmtResult, ExecByThmStmtSuccess,
    ExecReleaseThmStmtFailed, ExecReleaseThmStmtResult, ExecReleaseThmStmtSuccess,
};
use crate::ast::fact::{Fact, ForallFact};
use crate::ast::obj::Obj;
use crate::ast::stmt::{ByThmStmt, ReleaseThmStmt, TheoremCall, TheoremCallArguments};
use crate::runtime::runtime_ids::IdentifierId;
use crate::runtime::{Runtime, RuntimeResult};
use std::collections::HashMap;

pub fn exec_release_thm_stmt(
    runtime: &mut Runtime,
    stmt: &ReleaseThmStmt,
) -> RuntimeResult<ExecReleaseThmStmtResult> {
    let thm_name = stmt.call.name.local_name().to_string();
    let prepared = match prepare_release_conclusions(runtime, &stmt.call)? {
        Ok(p) => p,
        Err(failed) => return Ok(ExecReleaseThmStmtResult::Failed(failed)),
    };

    let (dom_outcome, local_env) = runtime.run_in_local_env_and_take_env(|rt| {
        let type_proofs = match verify_prepared_type_facts(rt, &thm_name, &prepared.type_facts)? {
            Ok(proofs) => proofs,
            Err(failed) => return Ok(Err(failed)),
        };
        let function_domain = match verify_prepared_function_domain(rt, &thm_name, &prepared.builtin)? {
            Ok(proof) => proof, Err(failed) => return Ok(Err(failed)),
        };
        let mut dom_proofs = Vec::with_capacity(prepared.dom_facts.len());
        for (index, dom) in prepared.dom_facts.iter().enumerate() {
            let proof = verify_goal_fact(rt, dom)?;
            if proof.is_failed() {
                return Ok(Err(ExecReleaseThmStmtFailed::Dom { theorem: thm_name.clone(), fact: dom.clone(), index, result: proof }));
            }
            let _ = rt.store_fact_and_infer(dom, crate::execute::execute_fact_stmt::VerifyState::top_level())?;
            dom_proofs.push(proof);
        }
        let conclusions_wd = match verify_prepared_conclusions_wd(rt, &thm_name, &prepared.conclusions)? {
            Ok(proofs) => proofs, Err(failed) => return Ok(Err(failed)),
        };
        Ok(Ok((type_proofs, function_domain, dom_proofs, conclusions_wd)))
    })?;

    let (type_proofs, function_domain, dom_proofs, conclusions_wd) = match dom_outcome {
        Ok(p) => p,
        Err(failed) => return Ok(ExecReleaseThmStmtResult::Failed(failed)),
    };

    let mut stored = Vec::with_capacity(prepared.conclusions.len());
    for (index, conclusion) in prepared.conclusions.iter().enumerate() {
        match store_goal_fact(runtime, conclusion)? {
            Ok(s) => stored.push(s),
            Err(message) => {
                return Ok(ExecReleaseThmStmtResult::Failed(
                    ExecReleaseThmStmtFailed::Store { theorem: thm_name.clone(), index, message },
                ));
            }
        }
    }

    Ok(ExecReleaseThmStmtResult::Success(ExecReleaseThmStmtSuccess {
        thm_name,
        builtin: prepared.builtin,
        type_proofs,
        function_domain,
        dom_proofs,
        conclusions_wd,
        local_env,
        stored,
    }))
}

pub fn exec_by_thm_stmt(
    runtime: &mut Runtime,
    stmt: &ByThmStmt,
) -> RuntimeResult<ExecByStmtResult> {
    let thm_name = stmt.call.name.local_name().to_string();
    let prepared = match prepare_release_conclusions(runtime, &stmt.call)? {
        Ok(p) => p,
        Err(failed) => {
            return Ok(ExecByStmtResult::Thm(ExecByThmStmtResult::Failed(
                ExecByThmStmtFailed::Release(failed),
            )));
        }
    };

    let selected: Fact = stmt.selected_fact.clone().into();
    let (local_outcome, local_env) = runtime.run_in_local_env_and_take_env(|rt| {
        let type_proofs = match verify_prepared_type_facts(rt, &thm_name, &prepared.type_facts)? {
            Ok(proofs) => proofs,
            Err(failed) => return Ok(Err(ExecByThmStmtFailed::Release(failed))),
        };
        let function_domain = match verify_prepared_function_domain(rt, &thm_name, &prepared.builtin)? {
            Ok(proof) => proof,
            Err(failed) => return Ok(Err(ExecByThmStmtFailed::Release(failed))),
        };
        let mut dom_proofs = Vec::with_capacity(prepared.dom_facts.len());
        for (index, dom) in prepared.dom_facts.iter().enumerate() {
            let proof = verify_goal_fact(rt, dom)?;
            if proof.is_failed() {
                return Ok(Err(ExecByThmStmtFailed::Release(
                    ExecReleaseThmStmtFailed::Dom { theorem: thm_name.clone(), fact: dom.clone(), index, result: proof },
                )));
            }
            let _ = rt.store_fact_and_infer(dom, crate::execute::execute_fact_stmt::VerifyState::top_level())?;
            dom_proofs.push(proof);
        }
        let conclusions_wd = match verify_prepared_conclusions_wd(rt, &thm_name, &prepared.conclusions)? {
            Ok(proofs) => proofs,
            Err(failed) => return Ok(Err(ExecByThmStmtFailed::Release(failed))),
        };
        for conclusion in &prepared.conclusions {
            let _ = rt.store_fact_and_infer(conclusion, crate::execute::execute_fact_stmt::VerifyState::top_level())?;
        }
        let selected_proof = verify_goal_fact(rt, &selected)?;
        if selected_proof.is_failed() {
            return Ok(Err(ExecByThmStmtFailed::Selected { theorem: thm_name.clone(), fact: selected.clone(), result: selected_proof }));
        }
        Ok(Ok((type_proofs, function_domain, dom_proofs, conclusions_wd, selected_proof)))
    })?;

    let (type_proofs, function_domain, dom_proofs, conclusions_wd, selected_proof) = match local_outcome {
        Ok(v) => v,
        Err(failed) => {
            return Ok(ExecByStmtResult::Thm(ExecByThmStmtResult::Failed(failed)));
        }
    };

    let stored = match store_goal_fact(runtime, &selected)? {
        Ok(s) => s,
        Err(msg) => {
            return Ok(ExecByStmtResult::Thm(ExecByThmStmtResult::Failed(
                ExecByThmStmtFailed::Store { theorem: thm_name.clone(), message: msg },
            )));
        }
    };

    Ok(ExecByStmtResult::Thm(ExecByThmStmtResult::Success(
        ExecByThmStmtSuccess {
            thm_name,
            builtin: prepared.builtin,
            type_proofs,
            function_domain,
            dom_proofs,
            conclusions_wd,
            selected_proof,
            local_env,
            stored,
        },
    )))
}

fn verify_prepared_function_domain(
    runtime: &mut Runtime, theorem: &str,
    builtin: &Option<super::result::BuiltinThmApplication>,
) -> RuntimeResult<Result<Option<super::result::BuiltinFunctionDomainProof>, ExecReleaseThmStmtFailed>> {
    let Some(application) = builtin else { return Ok(Ok(None)); };
    use crate::builtin_theorem::BuiltinTheoremId;
    if application.theorem == BuiltinTheoremId::TupleEqualFromCoordinates {
        let target = match runtime.tuple_equality_domain(&application.arguments[0], &application.arguments[1])? {
            Ok(target) => target,
            Err(message) => return Ok(Err(ExecReleaseThmStmtFailed::BuiltinShape { theorem: application.theorem, message })),
        };
        let left = match runtime.verify_complete_function_domain(&application.arguments[0], &target, super::helper::proof_verify_state())? {
            Ok(proof) => proof,
            Err(result) => return Ok(Err(ExecReleaseThmStmtFailed::FunctionDomain { theorem: theorem.to_string(), result })),
        };
        let right = match runtime.verify_complete_function_domain(&application.arguments[1], &target, super::helper::proof_verify_state())? {
            Ok(proof) => proof,
            Err(result) => return Ok(Err(ExecReleaseThmStmtFailed::FunctionDomain { theorem: theorem.to_string(), result })),
        };
        return Ok(Ok(Some(super::result::BuiltinFunctionDomainProof::TupleEquality { left, right })));
    }
    if !matches!(application.theorem, BuiltinTheoremId::FunctionSetMember | BuiltinTheoremId::CartesianMemberFromCoordinates) {
        return Ok(Ok(None));
    }
    let target = if application.theorem == BuiltinTheoremId::CartesianMemberFromCoordinates {
        runtime.cart_definition_for_set(&application.arguments[1]).map(|cart| runtime.cart_function_signature(&cart))
    } else { runtime.function_space_signature(&application.arguments[1]) };
    let Some(target) = target else {
        return Ok(Err(ExecReleaseThmStmtFailed::BuiltinShape {
            theorem: application.theorem,
            message: "second argument must be a function or sequence set".to_string(),
        }));
    };
    // Check before pointwise premises or the conclusion are stored. In
    // particular, an empty forall cannot supply an exact empty-domain proof.
    Ok(match runtime.verify_complete_function_domain(
        &application.arguments[0], &target, super::helper::proof_verify_state(),
    )? {
        Ok(proof) => Ok(Some(super::result::BuiltinFunctionDomainProof::Membership(proof))),
        Err(result) => Err(ExecReleaseThmStmtFailed::FunctionDomain {
            theorem: theorem.to_string(), result,
        }),
    })
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
) -> RuntimeResult<Result<PreparedRelease, ExecReleaseThmStmtFailed>> {
    if let Some(prepared) = super::builtin_thm::prepare_builtin_thm(runtime, call)? {
        return Ok(prepared);
    }
    if let Some(def_thm) = runtime.def_thm_visible(&call.name).cloned() {
        let thm_name = call.name.local_name();
        return match &def_thm.fact {
            Fact::ForallFact(forall) => prepare_forall_release(runtime, forall, &call.arguments),
            other => match &call.arguments {
                TheoremCallArguments::Bare => Ok(Ok(PreparedRelease {
                    builtin: None,
                    type_facts: Vec::new(),
                    dom_facts: Vec::new(),
                    conclusions: vec![other.clone()],
                })),
                TheoremCallArguments::Parenthesized(_) => Ok(Err(ExecReleaseThmStmtFailed::Shape(
                    format!(
                        "release thm `{thm_name}`: non-forall theorem must be called without arguments"
                    ),
                ))),
            },
        };
    }

    if let Some(axiom) = runtime.axiom_visible(&call.name).cloned() {
        return prepare_forall_release(runtime, &axiom.forall_fact, &call.arguments);
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

fn verify_prepared_type_facts(
    runtime: &mut Runtime,
    thm_name: &str,
    type_facts: &[Fact],
) -> RuntimeResult<Result<Vec<crate::execute::execute_fact_stmt::VerifyFactResult>, ExecReleaseThmStmtFailed>> {
    let mut proofs = Vec::with_capacity(type_facts.len());
    for (index, fact) in type_facts.iter().enumerate() {
        let proof = verify_goal_fact(runtime, fact)?;
        if proof.is_failed() {
            return Ok(Err(ExecReleaseThmStmtFailed::Type { theorem: thm_name.to_string(), fact: fact.clone(), index, result: proof }));
        }
        let _ = runtime.store_fact_and_infer(fact, crate::execute::execute_fact_stmt::VerifyState::top_level())?;
        proofs.push(proof);
    }
    Ok(Ok(proofs))
}

fn verify_prepared_conclusions_wd(
    runtime: &mut Runtime, thm_name: &str, conclusions: &[Fact],
) -> RuntimeResult<Result<Vec<crate::execute::execute_fact_stmt::FactWellDefinedProof>, ExecReleaseThmStmtFailed>> {
    use crate::execute::execute_fact_stmt::VerifyFactWellDefinedResult;
    let mut proofs = Vec::with_capacity(conclusions.len());
    for (index, fact) in conclusions.iter().enumerate() {
        let result = runtime.verify_fact_well_definedness(fact, super::helper::proof_verify_state())?;
        match result {
            VerifyFactWellDefinedResult::Success(proof) => proofs.push(proof),
            failed => return Ok(Err(ExecReleaseThmStmtFailed::ConclusionWd { theorem: thm_name.to_string(), fact: fact.clone(), index, result: failed })),
        }
    }
    Ok(Ok(proofs))
}
