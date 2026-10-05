//! `by fn_extension`: equal complete domains and pointwise equal values.
//!
//! Mathematical property: function extensionality on a shared carrier.
//! Return upper bounds do not identify the function. Each application layer
//! proves its own full-domain equality; returned functions are not flattened.
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
use crate::ast::obj::{FnObj, FnObjHead, FnSet, FunctionSpace, IdentifierObj, Obj};
use crate::ast::param::{ParamType, TypedParameterGroup, TypedParameterList};
use crate::ast::stmt::ByFnExtensionStmt;
use crate::execute::execute_fact_stmt::function_domain::FunctionDomainComparisonProof;
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

    let right_sources = runtime.complete_function_domains(&stmt.right, proof_verify_state())?;
    let mut failures = Vec::new();
    let mut matched = None;
    for right_source in right_sources {
        match runtime.verify_complete_function_domain(
            &stmt.left, &right_source.signature, proof_verify_state(),
        )? {
            Ok(domain_match) => { matched = Some((right_source, domain_match)); break; }
            Err(result) => failures.push(super::result::FnExtensionDomainCandidateFailure {
                right_source, result,
            }),
        }
    }
    let Some((right_domain, domain_match)) = matched else {
        return Ok(ExecByStmtResult::FnExtension(ExecByFnExtensionStmtResult::Failed(
            ExecByFnExtensionStmtFailed::DomainMatch(failures),
        )));
    };
    let left_fn_set = domain_match.source.signature.clone();

    let Some(pointwise) =
        build_pointwise_forall(runtime, &stmt.left, &stmt.right, &left_fn_set)?
    else {
        return Ok(ExecByStmtResult::FnExtension(
            ExecByFnExtensionStmtResult::Failed(ExecByFnExtensionStmtFailed::NoCompatibleFnSet),
        ));
    };

    let (local_outcome, local_env) = runtime.run_in_local_env_and_take_env(|rt| {
        // These facts were proved by the domain stage. Publish them only in
        // this proof scope, so pointwise WD can use the checked inclusions.
        if let FunctionDomainComparisonProof::MutualInclusion { forward, reverse, .. } = &domain_match.comparison {
            rt.store_fact_and_infer(forward, proof_verify_state())?;
            rt.store_fact_and_infer(reverse, proof_verify_state())?;
        }
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
            right_domain,
            domain_match,
            carrier: left_fn_set,
            proof_steps,
            pointwise_proof,
            local_env,
            stored,
        }),
    ))
}

fn build_pointwise_forall(
    runtime: &mut Runtime,
    left: &Obj,
    right: &Obj,
    carrier: &FnSet,
) -> RuntimeResult<Option<Fact>> {
    let mut typed_groups = Vec::new();
    let mut dom_facts = Vec::new();
    let mut arguments = Vec::new();
    let mut subst: HashMap<IdentifierId, Obj> = HashMap::new();
    for group in &carrier.set_bound_parameters.groups {
        let mut params = Vec::new();
        for old in &group.params {
            let fresh = runtime.fresh_internal_param();
            let value = Obj::Identifier(IdentifierObj::from_bound_name(&fresh));
            subst.insert(old.id, value.clone());
            arguments.push(value);
            params.push(fresh);
        }
        let Ok(param_type) = runtime.inst_obj(&group.param_type, &subst) else { return Ok(None); };
        typed_groups.push(TypedParameterGroup { params, param_type: ParamType::Obj(param_type) });
    }
    for guard in &carrier.dom_facts {
        let Ok(guard) = runtime.inst_quantifier_free_fact(guard, &subst) else { return Ok(None); };
        dom_facts.push(quantifier_free_fact_to_fact(guard));
    }
    let Some(left_ap) = apply_fn_layer(left, &arguments) else { return Ok(None); };
    let Some(right_ap) = apply_fn_layer(right, &arguments) else { return Ok(None); };
    Ok(Some(Fact::ForallFact(ForallFact {
        fact_id: runtime.global_ids.allocate_fact_id(),
        typed_parameters: TypedParameterList { groups: typed_groups }, dom_facts,
        then_facts: vec![ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(EqualFact {
            fact_id: runtime.global_ids.allocate_fact_id(), left: left_ap, right: right_ap, line_file: None,
        }))], line_file: None,
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
