//! `by fn_extension`: prove `f = g` from pointwise equality on alpha-equivalent FnSets.
//!
//! Mathematical property: function extensionality on a shared carrier.
//! When both sides have alpha-equivalent FnSet signatures, agreement on every
//! argument tuple of that signature yields ordinary object equality.
//!
//! Example:
//!   have fn f(x R) R = x
//!   have fn g(x R) R = x
//!   by fn_extension f = g

use crate::execute::execute_proof_block_stmt::run_proof_body_stmts;
use super::helper::{
    proof_verify_state, store_goal_fact, verify_goal_fact,
};
use super::result::{
    ExecByFnExtensionStmtFailed, ExecByFnExtensionStmtResult, ExecByFnExtensionStmtSuccess,
    ExecByStmtResult,
};
use crate::ast::fact::{
    AtomicFact, EqualFact, ExistOrAndChainAtomicFact, Fact, ForallFact,
};
use crate::ast::names::BoundName;
use crate::ast::obj::{FnObj, FnObjHead, FnSet, FunctionSpace, IdentifierObj, Obj};
use crate::ast::param::{ParamType, TypedParameterGroup, TypedParameterList};
use crate::ast::stmt::ByFnExtensionStmt;
use crate::execute::execute_fact_stmt::fn_sets_alpha_equal;
use crate::instantiate::quantifier_free_fact_to_fact;
use crate::runtime::runtime_ids::IdentifierId;
use crate::runtime::{Runtime, RuntimeResult};
use std::collections::HashMap;

// `by fn_extension`: prove equality from pointwise forall over alpha-equivalent FnSets.
pub fn exec_by_fn_extension_stmt(
    runtime: &mut Runtime,
    stmt: &ByFnExtensionStmt,
) -> RuntimeResult<ExecByStmtResult> {
    let goal: Fact = EqualFact {
        fact_id: runtime.global_ids.allocate_fact_id(),
        left: stmt.left.clone(),
        right: stmt.right.clone(),
        line_file: Some(stmt.line_file.clone()),
    }
    .into();

    let goal_wd = runtime.verify_fact_well_definedness(&goal, proof_verify_state())?;
    if goal_wd.is_failed() {
        return Ok(ExecByStmtResult::FnExtension(
            ExecByFnExtensionStmtResult::Failed(ExecByFnExtensionStmtFailed::GoalWd(goal_wd)),
        ));
    }

    let Some(left_fn_set) = resolve_fn_set_for_fn_extension(runtime, &stmt.left) else {
        return Ok(ExecByStmtResult::FnExtension(
            ExecByFnExtensionStmtResult::Failed(ExecByFnExtensionStmtFailed::NoCompatibleFnSet),
        ));
    };
    let Some(right_fn_set) = resolve_fn_set_for_fn_extension(runtime, &stmt.right) else {
        return Ok(ExecByStmtResult::FnExtension(
            ExecByFnExtensionStmtResult::Failed(ExecByFnExtensionStmtFailed::NoCompatibleFnSet),
        ));
    };
    if !fn_sets_alpha_equal(&left_fn_set, &right_fn_set) {
        return Ok(ExecByStmtResult::FnExtension(
            ExecByFnExtensionStmtResult::Failed(ExecByFnExtensionStmtFailed::NoCompatibleFnSet),
        ));
    }

    let Some(pointwise) =
        build_pointwise_forall(runtime, &stmt.left, &stmt.right, &left_fn_set)?
    else {
        return Ok(ExecByStmtResult::FnExtension(
            ExecByFnExtensionStmtResult::Failed(ExecByFnExtensionStmtFailed::NoCompatibleFnSet),
        ));
    };

    let (local_outcome, local_env) = runtime.run_in_local_env_and_take_env(|rt| {
        let proof_steps = match run_proof_body_stmts(rt, &stmt.proof)? {
            Ok(steps) => steps,
            Err(failed) => {
                return Ok(Err(ExecByFnExtensionStmtFailed::ProofBody(failed)));
            }
        };
        let pointwise_proof = verify_goal_fact(rt, &pointwise)?;
        if pointwise_proof.is_failed() {
            return Ok(Err(ExecByFnExtensionStmtFailed::Pointwise(pointwise_proof)));
        }
        Ok(Ok((proof_steps, pointwise_proof)))
    })?;

    let (proof_steps, pointwise_proof) = match local_outcome {
        Ok(v) => v,
        Err(failed) => {
            return Ok(ExecByStmtResult::FnExtension(
                ExecByFnExtensionStmtResult::Failed(failed),
            ));
        }
    };

    let stored = match store_goal_fact(runtime, &goal)? {
        Ok(s) => s,
        Err(msg) => {
            return Ok(ExecByStmtResult::FnExtension(
                ExecByFnExtensionStmtResult::Failed(ExecByFnExtensionStmtFailed::Store(msg)),
            ));
        }
    };

    Ok(ExecByStmtResult::FnExtension(
        ExecByFnExtensionStmtResult::Success(ExecByFnExtensionStmtSuccess {
            goal_wd,
            carrier: left_fn_set,
            proof_steps,
            pointwise_proof,
            local_env,
            stored,
        }),
    ))
}

fn resolve_fn_set_for_fn_extension(runtime: &Runtime, function: &Obj) -> Option<FnSet> {
    if let Obj::FunctionSpace(FunctionSpace::AnonymousFn(anon)) = function {
        return Some(anon.body.clone());
    }
    if let Obj::FunctionSpace(FunctionSpace::FnSet(fn_set)) = function {
        return Some(fn_set.clone());
    }
    runtime
        .collect_in_function_set_candidates(function)
        .into_iter()
        .next()
        .map(|(fn_set, _)| fn_set)
}

fn build_pointwise_forall(
    runtime: &mut Runtime,
    left: &Obj,
    right: &Obj,
    carrier: &FnSet,
) -> RuntimeResult<Option<Fact>> {
    let mut typed_groups: Vec<TypedParameterGroup> = Vec::new();
    let mut dom_facts: Vec<Fact> = Vec::new();
    let mut left_ap = left.clone();
    let mut right_ap = right.clone();
    let mut space = carrier.clone();
    let mut subst: HashMap<IdentifierId, Obj> = HashMap::new();

    loop {
        let mut layer_args: Vec<Obj> = Vec::new();
        for group in &space.set_bound_parameters.groups {
            let param_type_obj = match runtime.inst_obj(group.param_type.as_ref(), &subst) {
                Ok(o) => o,
                Err(_) => return Ok(None),
            };
            let mut fresh_params: Vec<BoundName> = Vec::new();
            for old in &group.params {
                let fresh = runtime.fresh_internal_param();
                let obj = Obj::Identifier(IdentifierObj::from_bound_name(&fresh));
                subst.insert(old.id, obj.clone());
                layer_args.push(obj);
                fresh_params.push(fresh);
            }
            if fresh_params.is_empty() {
                continue;
            }
            typed_groups.push(TypedParameterGroup {
                params: fresh_params,
                param_type: ParamType::Obj(param_type_obj),
            });
        }
        if layer_args.is_empty() {
            return Ok(None);
        }

        for dom in &space.dom_facts {
            let Ok(qf) = runtime.inst_quantifier_free_fact(dom, &subst) else {
                return Ok(None);
            };
            dom_facts.push(quantifier_free_fact_to_fact(qf));
        }

        let Some(next_left) = apply_fn_layer(&left_ap, &layer_args) else {
            return Ok(None);
        };
        let Some(next_right) = apply_fn_layer(&right_ap, &layer_args) else {
            return Ok(None);
        };
        left_ap = next_left;
        right_ap = next_right;

        let next_ret = match runtime.inst_obj(space.ret_set.as_ref(), &subst) {
            Ok(o) => o,
            Err(_) => return Ok(None),
        };
        match next_ret {
            Obj::FunctionSpace(FunctionSpace::FnSet(inner)) => {
                space = inner;
            }
            Obj::FunctionSpace(FunctionSpace::AnonymousFn(anon)) => {
                space = anon.body;
            }
            _ => break,
        }
    }

    if typed_groups.is_empty() {
        return Ok(None);
    }

    Ok(Some(Fact::ForallFact(ForallFact {
        fact_id: runtime.global_ids.allocate_fact_id(),
        typed_parameters: TypedParameterList {
            groups: typed_groups,
        },
        dom_facts,
        then_facts: vec![ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(
            EqualFact {
                fact_id: runtime.global_ids.allocate_fact_id(),
                left: left_ap,
                right: right_ap,
                line_file: None,
            },
        ))],
        line_file: None,
    })))
}

fn apply_fn_layer(function: &Obj, args: &[Obj]) -> Option<Obj> {
    let head = match function {
        Obj::Identifier(id) => FnObjHead::Identifier(id.clone()),
        Obj::FnObj(existing) => {
            let mut body = existing.body.clone();
            body.push(args.iter().cloned().map(Box::new).collect());
            return Some(Obj::FnObj(FnObj {
                head: existing.head.clone(),
                body,
            }));
        }
        Obj::FunctionSpace(FunctionSpace::AnonymousFn(af)) => {
            FnObjHead::AnonymousFnLiteral(Box::new(af.clone()))
        }
        Obj::StructAndFieldAccessObj(
            crate::ast::obj::StructAndFieldAccessObj::FieldAccess(fa),
        ) => FnObjHead::FieldAccess(fa.clone()),
        Obj::InstantiatedTemplateObj(t) => FnObjHead::InstantiatedTemplateObj(t.clone()),
        _ => return None,
    };
    Some(Obj::FnObj(FnObj {
        head: Box::new(head),
        body: vec![args.iter().cloned().map(Box::new).collect()],
    }))
}
