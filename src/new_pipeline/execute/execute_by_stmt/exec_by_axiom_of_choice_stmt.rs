use super::helper::{
    proof_verify_state, run_fact_only_proof_steps, store_goal_fact, verify_goal_fact,
};
use super::result::{
    ExecByAxiomOfChoiceStmtFailed, ExecByAxiomOfChoiceStmtResult, ExecByAxiomOfChoiceStmtSuccess,
    ExecByStmtResult,
};
use crate::new_pipeline::ast::fact::{
    AtomicFact, ExistOrAndChainAtomicFact, Fact, ForallFact, IsNonemptySetFact, IsSetFact, NormalAtomicFact,
    PlainExistFact, QuantifierFreeFact,
};
use crate::new_pipeline::ast::line_file::LineFile;
use crate::new_pipeline::ast::names::AtomicName;
use crate::new_pipeline::ast::obj::{AnonymousFn, FamilyUnion, FnSet, IdentifierObj, Obj, FunctionSpace, SetOperator};
use crate::new_pipeline::ast::param::{
    ParamType, SetBoundParameterGroup, SetBoundParameterList, TypedParameterGroup, TypedParameterList,
};
use crate::new_pipeline::ast::stmt::ByAxiomOfChoiceStmt;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

pub fn exec_by_axiom_of_choice_stmt(
    runtime: &mut Runtime,
    stmt: &ByAxiomOfChoiceStmt,
) -> RuntimeResult<ExecByStmtResult> {
    let family_wd =
        runtime.verify_obj_well_definedness(&stmt.family, proof_verify_state())?;
    if family_wd.is_failed() {
        return Ok(ExecByStmtResult::AxiomOfChoice(
            ExecByAxiomOfChoiceStmtResult::Failed(ExecByAxiomOfChoiceStmtFailed::FamilyWd(
                family_wd,
            )),
        ));
    }

    let obligations = ac_obligations(runtime, &stmt.family, &stmt.line_file);
    let (local_outcome, local_env) = runtime.run_in_local_env_and_take_env(|rt| {
        let proof_steps = match run_fact_only_proof_steps(rt, &stmt.proof)? {
            Ok(steps) => steps,
            Err(failed) => return Ok(Err(ExecByAxiomOfChoiceStmtFailed::ProofBody(failed))),
        };
        let mut obligation_proofs = Vec::with_capacity(obligations.len());
        for (index, obligation) in obligations.iter().enumerate() {
            let proof = verify_goal_fact(rt, obligation)?;
            if proof.is_failed() {
                return Ok(Err(ExecByAxiomOfChoiceStmtFailed::Obligation {
                    index,
                    result: proof,
                }));
            }
            let _ = store_goal_fact(rt, obligation)?;
            obligation_proofs.push(proof);
        }
        Ok(Ok((proof_steps, obligation_proofs)))
    })?;

    let (proof_steps, obligation_proofs) = match local_outcome {
        Ok(v) => v,
        Err(failed) => {
            return Ok(ExecByStmtResult::AxiomOfChoice(
                ExecByAxiomOfChoiceStmtResult::Failed(failed),
            ));
        }
    };

    // Trusted AC step. Selection stays atomic:
    // exist f fn(A S) family_union(S) st { $is_choice_function_for(S, S, fn(A S) S {A}, f) }.
    let choice_fact = ac_exist_fact(runtime, &stmt.family, &stmt.line_file);
    let stored = match store_goal_fact(runtime, &choice_fact)? {
        Ok(s) => s,
        Err(msg) => {
            return Ok(ExecByStmtResult::AxiomOfChoice(
                ExecByAxiomOfChoiceStmtResult::Failed(ExecByAxiomOfChoiceStmtFailed::Store(msg)),
            ));
        }
    };

    Ok(ExecByStmtResult::AxiomOfChoice(
        ExecByAxiomOfChoiceStmtResult::Success(ExecByAxiomOfChoiceStmtSuccess {
            family_wd,
            proof_steps,
            obligations: obligation_proofs,
            local_env,
            stored,
        }),
    ))
}

fn ac_obligations(runtime: &mut Runtime, family: &Obj, line_file: &LineFile) -> Vec<Fact> {
    let is_set: Fact = IsSetFact {
        fact_id: runtime.global_ids.allocate_fact_id(),
        set: family.clone(),
        line_file: Some(line_file.clone()),
    }
    .into();
    vec![is_set, ac_members_nonempty(runtime, family, line_file)]
}

fn ac_members_nonempty(runtime: &mut Runtime, family: &Obj, line_file: &LineFile) -> Fact {
    let a = runtime.fresh_internal_param();
    let a_obj = Obj::Identifier(IdentifierObj::from_bound_name(&a));
    let nonempty: AtomicFact = IsNonemptySetFact {
        fact_id: runtime.global_ids.allocate_fact_id(),
        set: a_obj,
        line_file: Some(line_file.clone()),
    }
    .into();
    Fact::ForallFact(ForallFact {
        fact_id: runtime.global_ids.allocate_fact_id(),
        typed_parameters: TypedParameterList {
            groups: vec![TypedParameterGroup {
                params: vec![a],
                param_type: ParamType::Obj(family.clone()),
            }],
        },
        dom_facts: vec![],
        then_facts: vec![ExistOrAndChainAtomicFact::AtomicFact(nonempty)],
        line_file: Some(line_file.clone()),
    })
}

fn ac_exist_fact(runtime: &mut Runtime, family: &Obj, line_file: &LineFile) -> Fact {
    let idx = runtime.fresh_internal_param();
    let fn_set = FnSet {
        set_bound_parameters: SetBoundParameterList {
            groups: vec![SetBoundParameterGroup {
                params: vec![idx],
                param_type: Box::new(family.clone()),
            }],
        },
        dom_facts: vec![],
        ret_set: Box::new(Obj::SetOperator(SetOperator::FamilyUnion(FamilyUnion {
            left: Box::new(family.clone()),
        }))),
    };
    let f = runtime.fresh_internal_param();
    let f_obj = Obj::Identifier(IdentifierObj::from_bound_name(&f));
    let id_idx = runtime.fresh_internal_param();
    let id_val = Obj::Identifier(IdentifierObj::from_bound_name(&id_idx));
    let identity = Obj::FunctionSpace(FunctionSpace::AnonymousFn(AnonymousFn {
        body: FnSet {
            set_bound_parameters: SetBoundParameterList {
                groups: vec![SetBoundParameterGroup {
                    params: vec![id_idx],
                    param_type: Box::new(family.clone()),
                }],
            },
            dom_facts: vec![],
            ret_set: Box::new(family.clone()),
        },
        equal_to: Box::new(id_val),
    }));
    let named: AtomicFact = NormalAtomicFact {
        fact_id: runtime.global_ids.allocate_fact_id(),
        predicate: AtomicName::plain("is_choice_function_for".to_string()),
        body: vec![family.clone(), family.clone(), identity, f_obj],
        line_file: Some(line_file.clone()),
    }
    .into();
    Fact::ExistFact(PlainExistFact {
        fact_id: runtime.global_ids.allocate_fact_id(),
        typed_parameters: TypedParameterList {
            groups: vec![TypedParameterGroup {
                params: vec![f],
                param_type: ParamType::Obj(Obj::FunctionSpace(FunctionSpace::FnSet(fn_set))),
            }],
        },
        facts: vec![QuantifierFreeFact::AtomicFact(named)],
        line_file: Some(line_file.clone()),
    })
}
