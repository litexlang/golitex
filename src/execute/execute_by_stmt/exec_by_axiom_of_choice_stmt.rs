use super::helper::{
    proof_verify_state, run_fact_only_proof_steps, store_goal_fact, verify_goal_fact,
};
use super::result::{
    ExecReleaseAxiomOfChoiceStmtFailed, ExecReleaseAxiomOfChoiceStmtResult,
    ExecReleaseAxiomOfChoiceStmtSuccess,
};
use crate::ast::fact::{
    AtomicFact, ExistOrAndChainAtomicFact, Fact, ForallFact, IsChoiceFunctionForFact,
    IsNonemptySetFact, IsSetFact, PlainExistFact, QuantifierFreeFact,
};
use crate::ast::line_file::SourceLine;
use crate::ast::obj::{AnonymousFn, FamilyUnion, FnSet, IdentifierObj, Obj, FunctionSpace, SetOperator};
use crate::ast::param::{
    ParamType, SetBoundParameterGroup, SetBoundParameterList, TypedParameterGroup, TypedParameterList,
};
use crate::ast::stmt::ReleaseAxiomOfChoiceStmt;
use crate::runtime::{Runtime, RuntimeResult};

pub fn exec_release_axiom_of_choice_stmt(
    runtime: &mut Runtime,
    stmt: &ReleaseAxiomOfChoiceStmt,
) -> RuntimeResult<ExecReleaseAxiomOfChoiceStmtResult> {
    let family_wd =
        runtime.verify_obj_well_definedness(&stmt.family, proof_verify_state())?;
    if family_wd.is_failed() {
        return Ok(ExecReleaseAxiomOfChoiceStmtResult::Failed(
            ExecReleaseAxiomOfChoiceStmtFailed::FamilyWd(family_wd),
        ));
    }

    let obligations = ac_obligations(runtime, &stmt.family, &stmt.line_file);
    let (local_outcome, local_env) = runtime.run_in_local_env_and_take_env(|rt| {
        let proof_steps = match run_fact_only_proof_steps(rt, &stmt.proof)? {
            Ok(steps) => steps,
            Err(failed) => return Ok(Err(ExecReleaseAxiomOfChoiceStmtFailed::ProofBody(failed))),
        };
        let mut obligation_proofs = Vec::with_capacity(obligations.len());
        for (index, obligation) in obligations.iter().enumerate() {
            let proof = verify_goal_fact(rt, obligation)?;
            if proof.is_failed() {
                return Ok(Err(ExecReleaseAxiomOfChoiceStmtFailed::Obligation {
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
            return Ok(ExecReleaseAxiomOfChoiceStmtResult::Failed(failed));
        }
    };

    // Trusted AC step. Selection stays atomic:
    // exist f fn(A S) family_union(S) st { $is_choice_function_for(S, S, fn(A S) S {A}, f) }.
    let choice_fact = ac_exist_fact(runtime, &stmt.family, &stmt.line_file);
    let stored = match store_goal_fact(runtime, &choice_fact)? {
        Ok(s) => s,
        Err(msg) => {
            return Ok(ExecReleaseAxiomOfChoiceStmtResult::Failed(
                ExecReleaseAxiomOfChoiceStmtFailed::Store(msg),
            ));
        }
    };

    Ok(ExecReleaseAxiomOfChoiceStmtResult::Success(
        ExecReleaseAxiomOfChoiceStmtSuccess {
            family_wd,
            proof_steps,
            obligations: obligation_proofs,
            local_env,
            stored,
        },
    ))
}

fn ac_obligations(runtime: &mut Runtime, family: &Obj, line_file: &SourceLine) -> Vec<Fact> {
    let is_set: Fact = IsSetFact {
        fact_id: runtime.global_ids.allocate_fact_id(),
        set: family.clone(),
        line_file: Some(line_file.clone()),
    }
    .into();
    vec![is_set, ac_members_nonempty(runtime, family, line_file)]
}

fn ac_members_nonempty(runtime: &mut Runtime, family: &Obj, line_file: &SourceLine) -> Fact {
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

fn ac_exist_fact(runtime: &mut Runtime, family: &Obj, line_file: &SourceLine) -> Fact {
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
    let named = AtomicFact::IsChoiceFunctionForFact(IsChoiceFunctionForFact {
        fact_id: runtime.global_ids.allocate_fact_id(),
        index: family.clone(),
        set: family.clone(),
        family: identity,
        choice: f_obj,
        line_file: Some(line_file.clone()),
    });
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
