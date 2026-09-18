use crate::new_pipeline::parse::prop_registration_shape::{
    plain_prop_name, symmetric_prop_registration_from_forall,
};
use super::result::{
    ExecByStmtResult, ExecBySymmetricPropStmtFailed, ExecBySymmetricPropStmtResult,
    ExecBySymmetricPropStmtSuccess,
};
use crate::new_pipeline::ast::stmt::BySymmetricPropStmt;
use crate::new_pipeline::exec_env::exec_env::PropRewriteProperty;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

pub fn exec_by_symmetric_prop_stmt(
    runtime: &mut Runtime,
    stmt: &BySymmetricPropStmt,
) -> RuntimeResult<ExecByStmtResult> {
    let (prop, gather) = match symmetric_prop_registration_from_forall(&stmt.forall_fact) {
        Ok(v) => v,
        Err(msg) => {
            return Ok(ExecByStmtResult::SymmetricProp(
                ExecBySymmetricPropStmtResult::Failed(ExecBySymmetricPropStmtFailed::Shape(msg)),
            ));
        }
    };
    let name = plain_prop_name(&prop);
    let Some(definition) = runtime.def_prop_visible_in_stack(name) else {
        return Ok(ExecByStmtResult::SymmetricProp(
            ExecBySymmetricPropStmtResult::Failed(ExecBySymmetricPropStmtFailed::PropNotDefined(
                name.to_string(),
            )),
        ));
    };
    let arity = definition
        .typed_parameters
        .groups
        .iter()
        .map(|g| g.params.len())
        .sum::<usize>();
    if arity != gather.len() {
        return Ok(ExecByStmtResult::SymmetricProp(
            ExecBySymmetricPropStmtResult::Failed(ExecBySymmetricPropStmtFailed::WrongArity {
                prop: prop.clone(),
                expected: gather.len(),
                actual: arity,
            }),
        ));
    }

    let _ = &stmt.proof;
    let verify_state = VerifyState {
        can_use_forall_fact: true,
        can_use_rewrite: true,
        store_well_defined_fact: true,
    };
    let forall_proof = runtime.verify_forall_fact(&stmt.forall_fact, verify_state)?;
    if forall_proof.is_failed() {
        return Ok(ExecByStmtResult::SymmetricProp(
            ExecBySymmetricPropStmtResult::Failed(ExecBySymmetricPropStmtFailed::Forall(
                forall_proof,
            )),
        ));
    }

    runtime
        .top_exec_env_mut()
        .prop_rewrite_properties
        .entry(prop.clone())
        .or_default()
        .push(PropRewriteProperty::SymmetricArgumentPermutate(vec![gather]));

    Ok(ExecByStmtResult::SymmetricProp(
        ExecBySymmetricPropStmtResult::Success(ExecBySymmetricPropStmtSuccess {
            prop,
            forall_proof,
        }),
    ))
}
