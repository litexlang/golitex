use super::helper::{proof_verify_state, store_goal_fact, verify_goal_fact};
use super::result::{
    ExecByRegularityAxiomStmtFailed, ExecByRegularityAxiomStmtResult,
    ExecByRegularityAxiomStmtSuccess, ExecByStmtResult,
};
use crate::new_pipeline::ast::fact::{
    AtomicFact, EqualFact, Fact, IsNonemptySetFact, PlainExistFact, QuantifierFreeFact,
};
use crate::new_pipeline::ast::obj::{IdentifierObj, Intersect, ListSet, Obj, SetFormer, SetOperator};
use crate::new_pipeline::ast::param::{ParamType, TypedParameterGroup, TypedParameterList};
use crate::new_pipeline::ast::stmt::ByRegularityAxiomStmt;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

pub fn exec_by_regularity_axiom_stmt(
    runtime: &mut Runtime,
    stmt: &ByRegularityAxiomStmt,
) -> RuntimeResult<ExecByStmtResult> {
    let set_wd =
        runtime.verify_obj_well_definedness(&stmt.set, proof_verify_state())?;
    if set_wd.is_failed() {
        return Ok(ExecByStmtResult::RegularityAxiom(
            ExecByRegularityAxiomStmtResult::Failed(ExecByRegularityAxiomStmtFailed::SetWd(
                set_wd,
            )),
        ));
    }

    // Obligation: A is nonempty before the foundation step applies.
    // Example: by regularity_axiom(A) requires $is_nonempty_set(A).
    let nonempty: Fact = IsNonemptySetFact {
        fact_id: runtime.global_ids.allocate_fact_id(),
        set: stmt.set.clone(),
        line_file: Some(stmt.line_file.clone()),
    }
    .into();
    let nonempty_proof = verify_goal_fact(runtime, &nonempty)?;
    if nonempty_proof.is_failed() {
        return Ok(ExecByStmtResult::RegularityAxiom(
            ExecByRegularityAxiomStmtResult::Failed(ExecByRegularityAxiomStmtFailed::Nonempty(
                nonempty_proof,
            )),
        ));
    }

    // Trusted regularity/foundation step: every nonempty set A has a member
    // disjoint from A. Example: by regularity_axiom(A) stores
    // exist x A st {intersect(x, A) = {}}.
    let regularity_fact = regularity_axiom_exist_fact(runtime, &stmt.set, &stmt.line_file);
    let stored = match store_goal_fact(runtime, &regularity_fact)? {
        Ok(s) => s,
        Err(msg) => {
            return Ok(ExecByStmtResult::RegularityAxiom(
                ExecByRegularityAxiomStmtResult::Failed(ExecByRegularityAxiomStmtFailed::Store(
                    msg,
                )),
            ));
        }
    };

    Ok(ExecByStmtResult::RegularityAxiom(
        ExecByRegularityAxiomStmtResult::Success(ExecByRegularityAxiomStmtSuccess {
            set_wd,
            nonempty: nonempty_proof,
            stored,
        }),
    ))
}

fn regularity_axiom_exist_fact(
    runtime: &mut Runtime,
    set: &Obj,
    line_file: &crate::new_pipeline::ast::line_file::SourceLine,
) -> Fact {
    let x = runtime.fresh_internal_param();
    let x_obj = Obj::Identifier(IdentifierObj::from_bound_name(&x));
    let empty_set = Obj::SetFormer(SetFormer::ListSet(ListSet { list: vec![] }));
    let disjoint: AtomicFact = EqualFact {
        fact_id: runtime.global_ids.allocate_fact_id(),
        left: Obj::SetOperator(SetOperator::Intersect(Intersect {
            left: Box::new(x_obj),
            right: Box::new(set.clone()),
        })),
        right: empty_set,
        line_file: Some(line_file.clone()),
    }
    .into();
    Fact::ExistFact(PlainExistFact {
        fact_id: runtime.global_ids.allocate_fact_id(),
        typed_parameters: TypedParameterList {
            groups: vec![TypedParameterGroup {
                params: vec![x],
                param_type: ParamType::Obj(set.clone()),
            }],
        },
        facts: vec![QuantifierFreeFact::AtomicFact(disjoint)],
        line_file: Some(line_file.clone()),
    })
}
