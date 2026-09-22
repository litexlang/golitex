use std::collections::HashMap;

use super::helper::{
    assume_fact, proof_verify_state, run_fact_only_proof_steps, store_goal_fact, verify_goal_fact,
};
use super::result::{
    ByInducBodySuccess, ByInducCaseFailed, ByInducCaseSuccess, ExecByInducStmtFailed,
    ExecByInducStmtResult, ExecByInducStmtSuccess, ExecByStmtResult, ExecByStrongInducStmtFailed,
    ExecByStrongInducStmtResult, ExecByStrongInducStmtSuccess,
};
use crate::new_pipeline::ast::fact::{
    AtomicFact, EqualFact, ExistOrAndChainAtomicFact, Fact, ForallFact, GreaterEqualFact, InFact,
    LessEqualFact,
};
use crate::new_pipeline::ast::names::BoundName;
use crate::new_pipeline::ast::obj::{Add, IdentifierObj, Number, Obj, StandardSet};
use crate::new_pipeline::ast::param::{ParamType, TypedParameterGroup, TypedParameterList};
use crate::new_pipeline::ast::stmt::{ByInducStmt, ByStrongInducStmt, Stmt};
use crate::new_pipeline::execute::execute_fact_stmt::VerifyFactWellDefinedResult;
use crate::new_pipeline::runtime::runtime_ids::IdentifierId;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};
use crate::new_pipeline::store_fact_and_infer::StoreFactAndInferResult;

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
    let Some(param) = recover_param(stmt.param_binding, stmt.to_prove) else {
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

    let body = if structured {
        match run_structured(runtime, &stmt, &param, strong, &goal_facts)? {
            Ok(b) => b,
            Err(c) => {
                return Ok(ExecByInducStmtResult::Failed(ExecByInducStmtFailed::Case(c)));
            }
        }
    } else {
        match run_unstructured(runtime, &stmt, &param, strong, &goal_facts)? {
            Ok(b) => b,
            Err(c) => {
                return Ok(ExecByInducStmtResult::Failed(ExecByInducStmtFailed::Case(c)));
            }
        }
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

fn run_unstructured(
    runtime: &mut Runtime,
    stmt: &Parts<'_>,
    param: &BoundName,
    strong: bool,
    goal_facts: &[Fact],
) -> RuntimeResult<Result<ByInducBodySuccess, ByInducCaseFailed>> {
    let (inner, local_env) = runtime.run_in_local_env_and_take_env(|rt| {
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
        let proof_steps = match run_fact_only_proof_steps(rt, stmt.proof)? {
            Ok(s) => s,
            Err(e) => return Ok(Err(ByInducCaseFailed::ProofBody(e))),
        };
        let mut goals_verified = Vec::new();
        for (index, goal) in goal_facts.iter().enumerate() {
            let base = match inst_at(rt, goal, param.id, stmt.induc_from.clone()) {
                Ok(f) => f,
                Err(msg) => return Ok(Err(ByInducCaseFailed::Assume(msg))),
            };
            let base_proof = verify_goal_fact(rt, &base)?;
            if base_proof.is_failed() {
                return Ok(Err(ByInducCaseFailed::Goal {
                    index,
                    result: base_proof,
                }));
            }
            goals_verified.push(base_proof);

            // Prove P(n+1) under live `n` and IH; do not open a forall binder
            // named the same as `n` (stack name clash → InternalBug).
            let succ_goal = match inst_at(rt, goal, param.id, add_one(param_obj(param))) {
                Ok(f) => f,
                Err(msg) => return Ok(Err(ByInducCaseFailed::Assume(msg))),
            };
            let step_proof = verify_goal_fact(rt, &succ_goal)?;
            if step_proof.is_failed() {
                return Ok(Err(ByInducCaseFailed::Goal {
                    index,
                    result: step_proof,
                }));
            }
            goals_verified.push(step_proof);
        }
        Ok(Ok((assumptions_stored, proof_steps, goals_verified)))
    })?;

    match inner {
        Ok((assumptions_stored, proof_steps, goals_verified)) => {
            Ok(Ok(ByInducBodySuccess::Unstructured(ByInducCaseSuccess {
                assumptions_stored,
                proof_steps,
                goals_verified,
                local_env,
            })))
        }
        Err(e) => Ok(Err(e)),
    }
}

fn run_structured(
    runtime: &mut Runtime,
    stmt: &Parts<'_>,
    param: &BoundName,
    strong: bool,
    goal_facts: &[Fact],
) -> RuntimeResult<Result<ByInducBodySuccess, ByInducCaseFailed>> {
    let base_proof = stmt.base_proof.as_ref().expect("structured");
    let step_proof = stmt.step_proof.as_ref().expect("structured");

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

    Ok(Ok(ByInducBodySuccess::Structured { base, step }))
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
        fact_id: runtime.ids.allocate_fact_id(),
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
        fact_id: runtime.ids.allocate_fact_id(),
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

fn recover_param(name: &str, goals: &[ExistOrAndChainAtomicFact]) -> Option<BoundName> {
    for goal in goals {
        if let ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(eq)) = goal {
            if let Some(b) = bound_from_obj(name, &eq.left).or_else(|| bound_from_obj(name, &eq.right))
            {
                return Some(b);
            }
        }
        if let ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::NormalAtomicFact(n)) = goal {
            for obj in &n.body {
                if let Some(b) = bound_from_obj(name, obj) {
                    return Some(b);
                }
            }
        }
    }
    None
}

fn bound_from_obj(name: &str, obj: &Obj) -> Option<BoundName> {
    match obj {
        Obj::Identifier(IdentifierObj::Plain { id, name: n }) if n == name => {
            Some(BoundName::new(*id, n.clone()))
        }
        Obj::Add(Add { left, right }) => {
            bound_from_obj(name, left).or_else(|| bound_from_obj(name, right))
        }
        _ => None,
    }
}

fn param_obj(param: &BoundName) -> Obj {
    Obj::Identifier(IdentifierObj::from_bound_name(param))
}

fn add_one(obj: Obj) -> Obj {
    Obj::Add(Add {
        left: Box::new(obj),
        right: Box::new(Obj::Number(Number {
            normalized_value: "1".to_string(),
        })),
    })
}

fn mk_in_z(runtime: &mut Runtime, element: Obj) -> Fact {
    InFact {
        fact_id: runtime.ids.allocate_fact_id(),
        element,
        set: Obj::StandardSet(StandardSet::Z),
        line_file: None,
    }
    .into()
}

fn mk_greater_equal(runtime: &mut Runtime, left: Obj, right: Obj) -> Fact {
    GreaterEqualFact {
        fact_id: runtime.ids.allocate_fact_id(),
        left,
        right,
        line_file: None,
    }
    .into()
}

fn mk_less_equal(runtime: &mut Runtime, left: Obj, right: Obj) -> Fact {
    LessEqualFact {
        fact_id: runtime.ids.allocate_fact_id(),
        left,
        right,
        line_file: None,
    }
    .into()
}

fn mk_equal(runtime: &mut Runtime, left: Obj, right: Obj) -> Fact {
    EqualFact {
        fact_id: runtime.ids.allocate_fact_id(),
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
