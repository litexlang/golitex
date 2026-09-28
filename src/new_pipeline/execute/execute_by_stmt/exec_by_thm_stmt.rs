use super::helper::{store_goal_fact, verify_goal_fact};
use super::result::{
    ExecByStmtResult, ExecByThmStmtFailed, ExecByThmStmtResult, ExecByThmStmtSuccess,
    ExecReleaseThmStmtFailed, ExecReleaseThmStmtResult, ExecReleaseThmStmtSuccess,
};
use crate::new_pipeline::ast::fact::{Fact, ForallFact};
use crate::new_pipeline::ast::obj::Obj;
use crate::new_pipeline::ast::stmt::{ByThmStmt, ReleaseThmStmt, TheoremCall, TheoremCallArguments};
use crate::new_pipeline::runtime::runtime_ids::IdentifierId;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};
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
        let mut dom_proofs = Vec::with_capacity(prepared.dom_facts.len());
        for (index, dom) in prepared.dom_facts.iter().enumerate() {
            let proof = verify_goal_fact(rt, dom)?;
            if proof.is_failed() {
                return Ok(Err(ExecReleaseThmStmtFailed::Dom { index, result: proof }));
            }
            dom_proofs.push(proof);
        }
        Ok(Ok(dom_proofs))
    })?;

    let dom_proofs = match dom_outcome {
        Ok(p) => p,
        Err(failed) => return Ok(ExecReleaseThmStmtResult::Failed(failed)),
    };

    let mut stored = Vec::with_capacity(prepared.conclusions.len());
    for (index, conclusion) in prepared.conclusions.iter().enumerate() {
        match store_goal_fact(runtime, conclusion)? {
            Ok(s) => stored.push(s),
            Err(message) => {
                return Ok(ExecReleaseThmStmtResult::Failed(
                    ExecReleaseThmStmtFailed::Store { index, message },
                ));
            }
        }
    }

    Ok(ExecReleaseThmStmtResult::Success(ExecReleaseThmStmtSuccess {
        thm_name,
        dom_proofs,
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
        let mut dom_proofs = Vec::with_capacity(prepared.dom_facts.len());
        for (index, dom) in prepared.dom_facts.iter().enumerate() {
            let proof = verify_goal_fact(rt, dom)?;
            if proof.is_failed() {
                return Ok(Err(ExecByThmStmtFailed::Release(
                    ExecReleaseThmStmtFailed::Dom { index, result: proof },
                )));
            }
            let _ = rt.store_fact_and_infer(dom)?;
            dom_proofs.push(proof);
        }
        for conclusion in &prepared.conclusions {
            let _ = rt.store_fact_and_infer(conclusion)?;
        }
        let selected_proof = verify_goal_fact(rt, &selected)?;
        if selected_proof.is_failed() {
            return Ok(Err(ExecByThmStmtFailed::Selected(selected_proof)));
        }
        Ok(Ok((dom_proofs, selected_proof)))
    })?;

    let (dom_proofs, selected_proof) = match local_outcome {
        Ok(v) => v,
        Err(failed) => {
            return Ok(ExecByStmtResult::Thm(ExecByThmStmtResult::Failed(failed)));
        }
    };

    let stored = match store_goal_fact(runtime, &selected)? {
        Ok(s) => s,
        Err(msg) => {
            return Ok(ExecByStmtResult::Thm(ExecByThmStmtResult::Failed(
                ExecByThmStmtFailed::Store(msg),
            )));
        }
    };

    Ok(ExecByStmtResult::Thm(ExecByThmStmtResult::Success(
        ExecByThmStmtSuccess {
            thm_name,
            dom_proofs,
            selected_proof,
            local_env,
            stored,
        },
    )))
}

pub(crate) struct PreparedRelease {
    pub(crate) dom_facts: Vec<Fact>,
    pub(crate) conclusions: Vec<Fact>,
}

pub(crate) fn prepare_release_conclusions(
    runtime: &mut Runtime,
    call: &TheoremCall,
) -> RuntimeResult<Result<PreparedRelease, ExecReleaseThmStmtFailed>> {
    if let Some(def_thm) = runtime.def_thm_visible(&call.name).cloned() {
        let thm_name = call.name.local_name();
        return match &def_thm.fact {
            Fact::ForallFact(forall) => prepare_forall_release(runtime, forall, &call.arguments),
            other => match &call.arguments {
                TheoremCallArguments::Bare => Ok(Ok(PreparedRelease {
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
        dom_facts,
        conclusions,
    }))
}
