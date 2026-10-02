use std::collections::HashMap;

use super::helper::{
    assume_fact, proof_verify_state, recover_induction_param, run_fact_only_proof_steps, store_goal_fact, verify_goal_fact,
};
use super::result::{
    ByInducBodySuccess, ByInducCaseFailed, ByInducCaseSuccess, ExecByInducStmtFailed,
    ExecByInducStmtResult, ExecByInducStmtSuccess, ExecByStmtResult, ExecByStrongInducStmtFailed,
    ExecByStrongInducStmtResult, ExecByStrongInducStmtSuccess,
};
use crate::ast::fact::{
    AtomicFact, EqualFact, ExistOrAndChainAtomicFact, Fact, ForallFact, GreaterEqualFact, InFact,
    LessEqualFact,
};
use crate::ast::names::BoundName;
use crate::ast::obj::{Add, IdentifierObj, Number, Obj, StandardSet, ArithmeticOperator, Literal};
use crate::ast::param::{ParamType, TypedParameterGroup, TypedParameterList};
use crate::ast::stmt::{ByInducStmt, ByStrongInducStmt, Stmt};
use crate::execute::execute_fact_stmt::VerifyFactWellDefinedResult;
use crate::runtime::runtime_ids::IdentifierId;
use crate::runtime::{Runtime, RuntimeResult};
use crate::store_fact_and_infer::StoreFactAndInferResult;

// Integer `by induc` / `by strong_induc`.
// Stores a forall over `n Z` with premise `n >= from` and the inducted conclusion.
//
// Example:
//   by induc n from 0:
//       ? n = n
pub fn exec_by_induc_stmt(
    runtime: &mut Runtime,
    stmt: &ByInducStmt,
) -> RuntimeResult<ExecByStmtResult> {
    Ok(ExecByStmtResult::Induc(run_induc(
        runtime,
        Parts {
            to_prove: &stmt.to_prove,
            proof: &stmt.proof,
            base_proof: &stmt.base_proof,
            step_proof: &stmt.step_proof,
            param_binding: &stmt.param_binding,
            induc_from: &stmt.induc_from,
        },
        false,
    )?))
}

pub fn exec_by_strong_induc_stmt(
    runtime: &mut Runtime,
    stmt: &ByStrongInducStmt,
) -> RuntimeResult<ExecByStmtResult> {
    let result = run_induc(
        runtime,
        Parts {
            to_prove: &stmt.to_prove,
            proof: &stmt.proof,
            base_proof: &stmt.base_proof,
            step_proof: &stmt.step_proof,
            param_binding: &stmt.param_binding,
            induc_from: &stmt.induc_from,
        },
        true,
    )?;
    Ok(ExecByStmtResult::StrongInduc(match result {
        ExecByInducStmtResult::Success(s) => {
            ExecByStrongInducStmtResult::Success(ExecByStrongInducStmtSuccess {
                goals_wd: s.goals_wd,
                body: s.body,
                stored: s.stored,
            })
        }
        ExecByInducStmtResult::Failed(f) => ExecByStrongInducStmtResult::Failed(map_strong(f)),
    }))
}

struct Parts<'a> {
    to_prove: &'a [ExistOrAndChainAtomicFact],
    proof: &'a [Stmt],
    base_proof: &'a Option<Vec<Stmt>>,
    step_proof: &'a Option<Vec<Stmt>>,
    param_binding: &'a str,
    induc_from: &'a Obj,
}

fn run_induc(
    runtime: &mut Runtime,
    stmt: Parts<'_>,
    strong: bool,
) -> RuntimeResult<ExecByInducStmtResult> {
    let Some(param) = recover_induction_param(stmt.param_binding, stmt.to_prove) else {
        return Ok(failed_shape(format!(
            "by induc: cannot recover binder `{}` from goals",
            stmt.param_binding
        )));
    };

    let structured = stmt.base_proof.is_some() || stmt.step_proof.is_some();
    if structured && (stmt.base_proof.is_none() || stmt.step_proof.is_none()) {
        return Ok(failed_shape(
            "by induc: structured proof needs both `? from` and `? induc`/`? strong_induc`"
                .to_string(),
        ));
    }
    if structured && !stmt.proof.is_empty() {
        return Ok(failed_shape(
            "by induc: unstructured proof cannot mix with structured blocks".to_string(),
        ));
    }

    let from_in_z = mk_in_z(runtime, stmt.induc_from.clone());
    let from_ok = verify_goal_fact(runtime, &from_in_z)?;
    if from_ok.is_failed() {
        return Ok(ExecByInducStmtResult::Failed(ExecByInducStmtFailed::Case(
            ByInducCaseFailed::Goal {
                index: 0,
                result: from_ok,
            },
        )));
    }

    let goal_facts: Vec<Fact> = stmt.to_prove.iter().cloned().map(Into::into).collect();

    let (wd_res, _) = runtime.run_in_local_env_and_take_env(|rt| -> RuntimeResult<Result<Vec<VerifyFactWellDefinedResult>, ExecByInducStmtFailed>> {
        if let Err(msg) = intro_param_z(rt, &param)? {
            return Ok(Err(ExecByInducStmtFailed::BodyShape(msg)));
        }
        let mut wds = Vec::new();
        for (index, fact) in goal_facts.iter().enumerate() {
            let wd = rt.verify_fact_well_definedness(fact, proof_verify_state())?;
            if wd.is_failed() {
                return Ok(Err(ExecByInducStmtFailed::GoalWd { index, result: wd }));
            }
            wds.push(wd);
        }
        Ok(Ok(wds))
    })?;
    let goals_wd = match wd_res {
        Ok(w) => w,
        Err(e) => return Ok(ExecByInducStmtResult::Failed(e)),
    };

    let base_proof = stmt.base_proof.as_deref().unwrap_or(stmt.proof);
    let step_proof = stmt.step_proof.as_deref().unwrap_or(stmt.proof);
    let (base, step) = match run_induction_cases(
        runtime,
        &stmt,
        &param,
        strong,
        &goal_facts,
        base_proof,
        step_proof,
    )? {
        Ok(cases) => cases,
        Err(failed) => {
            return Ok(ExecByInducStmtResult::Failed(ExecByInducStmtFailed::Case(failed)));
        }
    };
    let body = if structured {
        ByInducBodySuccess::Structured { base, step }
    } else {
        ByInducBodySuccess::Unstructured { base, step }
    };

    let concluding = mk_concluding_forall(runtime, &param, stmt.induc_from, stmt.to_prove);
    let stored = match store_goal_fact(runtime, &concluding)? {
        Ok(s) => s,
        Err(msg) => {
            return Ok(ExecByInducStmtResult::Failed(ExecByInducStmtFailed::Store(
                msg,
            )));
        }
    };

    Ok(ExecByInducStmtResult::Success(ExecByInducStmtSuccess {
        goals_wd,
        body,
        stored,
    }))
}

fn run_induction_cases(
    runtime: &mut Runtime,
    stmt: &Parts<'_>,
    param: &BoundName,
    strong: bool,
    goal_facts: &[Fact],
    base_proof: &[Stmt],
    step_proof: &[Stmt],
) -> RuntimeResult<Result<(ByInducCaseSuccess, ByInducCaseSuccess), ByInducCaseFailed>> {

    let (base_inner, base_env) = runtime.run_in_local_env_and_take_env(|rt| {
        let mut assumptions_stored = Vec::new();
        if let Err(msg) = intro_param_z(rt, param)? {
            return Ok(Err(ByInducCaseFailed::Assume(msg)));
        }
        let n_eq_from = mk_equal(rt, param_obj(param), stmt.induc_from.clone());
        match assume_fact(rt, &n_eq_from)? {
            Ok(s) => assumptions_stored.push(s),
            Err(msg) => return Ok(Err(ByInducCaseFailed::Assume(msg))),
        }
        let proof_steps = match run_fact_only_proof_steps(rt, base_proof)? {
            Ok(s) => s,
            Err(e) => return Ok(Err(ByInducCaseFailed::ProofBody(e))),
        };
        let mut goals_verified = Vec::new();
        for (index, goal) in goal_facts.iter().enumerate() {
            let g = match inst_at(rt, goal, param.id, stmt.induc_from.clone()) {
                Ok(f) => f,
                Err(msg) => return Ok(Err(ByInducCaseFailed::Assume(msg))),
            };
            let proof = verify_goal_fact(rt, &g)?;
            if proof.is_failed() {
                return Ok(Err(ByInducCaseFailed::Goal {
                    index,
                    result: proof,
                }));
            }
            goals_verified.push(proof);
        }
        Ok(Ok((assumptions_stored, proof_steps, goals_verified)))
    })?;
    let base = match base_inner {
        Ok((assumptions_stored, proof_steps, goals_verified)) => ByInducCaseSuccess {
            assumptions_stored,
            proof_steps,
            goals_verified,
            local_env: base_env,
        },
        Err(e) => return Ok(Err(e)),
    };

    let (step_inner, step_env) = runtime.run_in_local_env_and_take_env(|rt| {
        let mut assumptions_stored = Vec::new();
        if let Err(msg) = intro_param_z(rt, param)? {
            return Ok(Err(ByInducCaseFailed::Assume(msg)));
        }
        let n_ge_from = mk_greater_equal(rt, param_obj(param), stmt.induc_from.clone());
        match assume_fact(rt, &n_ge_from)? {
            Ok(s) => assumptions_stored.push(s),
            Err(msg) => return Ok(Err(ByInducCaseFailed::Assume(msg))),
        }
        match store_ihs(rt, param, stmt.induc_from, goal_facts, strong)? {
            Ok(mut xs) => assumptions_stored.append(&mut xs),
            Err(e) => return Ok(Err(e)),
        }
        let proof_steps = match run_fact_only_proof_steps(rt, step_proof)? {
            Ok(s) => s,
            Err(e) => return Ok(Err(ByInducCaseFailed::ProofBody(e))),
        };
        let succ = add_one(param_obj(param));
        let mut goals_verified = Vec::new();
        for (index, goal) in goal_facts.iter().enumerate() {
            let g = match inst_at(rt, goal, param.id, succ.clone()) {
                Ok(f) => f,
                Err(msg) => return Ok(Err(ByInducCaseFailed::Assume(msg))),
            };
            let proof = verify_goal_fact(rt, &g)?;
            if proof.is_failed() {
                return Ok(Err(ByInducCaseFailed::Goal {
                    index,
                    result: proof,
                }));
            }
            goals_verified.push(proof);
        }
        Ok(Ok((assumptions_stored, proof_steps, goals_verified)))
    })?;
    let step = match step_inner {
        Ok((assumptions_stored, proof_steps, goals_verified)) => ByInducCaseSuccess {
            assumptions_stored,
            proof_steps,
            goals_verified,
            local_env: step_env,
        },
        Err(e) => return Ok(Err(e)),
    };

    Ok(Ok((base, step)))
}

fn intro_param_z(runtime: &mut Runtime, param: &BoundName) -> RuntimeResult<Result<(), String>> {
    let typed = TypedParameterList {
        groups: vec![TypedParameterGroup {
            params: vec![param.clone()],
            param_type: ParamType::Obj(Obj::StandardSet(StandardSet::Z)),
        }],
    };
    match runtime.introduce_typed_parameters(&typed, proof_verify_state())? {
        Ok(_) => Ok(Ok(())),
        Err(_) => Ok(Err(format!(
            "by induc: failed to introduce `{}` in Z",
            param.name
        ))),
    }
}

fn store_ihs(
    runtime: &mut Runtime,
    param: &BoundName,
    induc_from: &Obj,
    goals: &[Fact],
    strong: bool,
) -> RuntimeResult<Result<Vec<StoreFactAndInferResult>, ByInducCaseFailed>> {
    let mut out = Vec::new();
    if strong {
        for (index, goal) in goals.iter().enumerate() {
            let ih = match mk_strong_ih(runtime, param, induc_from, goal) {
                Ok(f) => f,
                Err(msg) => return Ok(Err(ByInducCaseFailed::Assume(msg))),
            };
            match assume_fact(runtime, &ih)? {
                Ok(s) => out.push(s),
                Err(msg) => {
                    return Ok(Err(ByInducCaseFailed::Assume(format!(
                        "strong IH {index}: {msg}"
                    ))));
                }
            }
        }
    } else {
        for (index, goal) in goals.iter().enumerate() {
            match assume_fact(runtime, goal)? {
                Ok(s) => out.push(s),
                Err(msg) => {
                    return Ok(Err(ByInducCaseFailed::Assume(format!(
                        "IH {index}: {msg}"
                    ))));
                }
            }
        }
    }
    Ok(Ok(out))
}

fn mk_strong_ih(
    runtime: &mut Runtime,
    param: &BoundName,
    induc_from: &Obj,
    goal: &Fact,
) -> Result<Fact, String> {
    // Fresh binder so the IH forall does not reuse the live induction param name
    // (`identifier_defined_in_stack` is name-based).
    let y = runtime.fresh_internal_param();
    let y_obj = param_obj(&y);
    let p_y = inst_at(runtime, goal, param.id, y_obj.clone())?;
    Ok(Fact::ForallFact(ForallFact {
        fact_id: runtime.global_ids.allocate_fact_id(),
        typed_parameters: TypedParameterList {
            groups: vec![TypedParameterGroup {
                params: vec![y],
                param_type: ParamType::Obj(Obj::StandardSet(StandardSet::Z)),
            }],
        },
        dom_facts: vec![
            mk_greater_equal(runtime, y_obj.clone(), induc_from.clone()),
            mk_less_equal(runtime, y_obj, param_obj(param)),
        ],
        then_facts: vec![to_exist_or_and(p_y)?],
        line_file: None,
    }))
}

fn mk_concluding_forall(
    runtime: &mut Runtime,
    param: &BoundName,
    induc_from: &Obj,
    goals: &[ExistOrAndChainAtomicFact],
) -> Fact {
    Fact::ForallFact(ForallFact {
        fact_id: runtime.global_ids.allocate_fact_id(),
        typed_parameters: TypedParameterList {
            groups: vec![TypedParameterGroup {
                params: vec![param.clone()],
                param_type: ParamType::Obj(Obj::StandardSet(StandardSet::Z)),
            }],
        },
        dom_facts: vec![mk_greater_equal(
            runtime,
            param_obj(param),
            induc_from.clone(),
        )],
        then_facts: goals.to_vec(),
        line_file: None,
    })
}

fn inst_at(
    runtime: &mut Runtime,
    goal: &Fact,
    param_id: IdentifierId,
    at: Obj,
) -> Result<Fact, String> {
    let mut map = HashMap::new();
    map.insert(param_id, at);
    runtime
        .inst_fact(goal, &map)
        .map_err(|e| format!("instantiate induction goal: {e}"))
}

fn to_exist_or_and(fact: Fact) -> Result<ExistOrAndChainAtomicFact, String> {
    match fact {
        Fact::AtomicFact(a) => Ok(ExistOrAndChainAtomicFact::AtomicFact(a)),
        Fact::AndFact(a) => Ok(ExistOrAndChainAtomicFact::AndFact(a)),
        Fact::ChainFact(c) => Ok(ExistOrAndChainAtomicFact::ChainFact(c)),
        Fact::OrFact(o) => Ok(ExistOrAndChainAtomicFact::OrFact(o)),
        Fact::ExistFact(e) => Ok(ExistOrAndChainAtomicFact::ExistFact(e)),
        Fact::ExistUniqueFact(e) => Ok(ExistOrAndChainAtomicFact::ExistUniqueFact(e)),
        Fact::NotExistFact(e) => Ok(ExistOrAndChainAtomicFact::NotExistFact(e)),
        _ => Err("induction goal must stay quantifier-free".to_string()),
    }
}

fn param_obj(param: &BoundName) -> Obj {
    Obj::Identifier(IdentifierObj::from_bound_name(param))
}

fn add_one(obj: Obj) -> Obj {
    Obj::ArithmeticOperator(ArithmeticOperator::Add(Add {
        left: Box::new(obj),
        right: Box::new(Obj::Literal(Literal::Number(Number {
            normalized_value: "1".to_string(),
        }))),
    }))
}

fn mk_in_z(runtime: &mut Runtime, element: Obj) -> Fact {
    InFact {
        fact_id: runtime.global_ids.allocate_fact_id(),
        element,
        set: Obj::StandardSet(StandardSet::Z),
        line_file: None,
    }
    .into()
}

fn mk_greater_equal(runtime: &mut Runtime, left: Obj, right: Obj) -> Fact {
    GreaterEqualFact {
        fact_id: runtime.global_ids.allocate_fact_id(),
        left,
        right,
        line_file: None,
    }
    .into()
}

fn mk_less_equal(runtime: &mut Runtime, left: Obj, right: Obj) -> Fact {
    LessEqualFact {
        fact_id: runtime.global_ids.allocate_fact_id(),
        left,
        right,
        line_file: None,
    }
    .into()
}

fn mk_equal(runtime: &mut Runtime, left: Obj, right: Obj) -> Fact {
    EqualFact {
        fact_id: runtime.global_ids.allocate_fact_id(),
        left,
        right,
        line_file: None,
    }
    .into()
}

fn failed_shape(msg: String) -> ExecByInducStmtResult {
    ExecByInducStmtResult::Failed(ExecByInducStmtFailed::BodyShape(msg))
}

fn map_strong(failed: ExecByInducStmtFailed) -> ExecByStrongInducStmtFailed {
    match failed {
        ExecByInducStmtFailed::GoalWd { index, result } => {
            ExecByStrongInducStmtFailed::GoalWd { index, result }
        }
        ExecByInducStmtFailed::BodyShape(s) => ExecByStrongInducStmtFailed::BodyShape(s),
        ExecByInducStmtFailed::Case(c) => ExecByStrongInducStmtFailed::Case(c),
        ExecByInducStmtFailed::Store(s) => ExecByStrongInducStmtFailed::Store(s),
        ExecByInducStmtFailed::NotFullyWired(s) => ExecByStrongInducStmtFailed::NotFullyWired(s),
    }
}
