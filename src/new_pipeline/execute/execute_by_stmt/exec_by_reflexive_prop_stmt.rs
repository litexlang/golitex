use crate::new_pipeline::parse::prop_registration_shape::{
    plain_prop_name, reflexive_prop_name_from_forall,
};
use super::result::{
    ExecByPropRegistrationStmtFailed, ExecByPropRegistrationStmtResult,
    ExecByPropRegistrationStmtSuccess, ExecByStmtResult,
};
use crate::new_pipeline::ast::stmt::ByReflexivePropStmt;
use crate::new_pipeline::exec_env::exec_env::PropRewriteProperty;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

pub fn exec_by_reflexive_prop_stmt(
    runtime: &mut Runtime,
    stmt: &ByReflexivePropStmt,
) -> RuntimeResult<ExecByStmtResult> {
    let prop = match reflexive_prop_name_from_forall(&stmt.forall_fact) {
        Ok(p) => p,
        Err(msg) => {
            return Ok(ExecByStmtResult::PropRegistration(
                ExecByPropRegistrationStmtResult::Failed(
                    ExecByPropRegistrationStmtFailed::Shape(msg),
                ),
            ));
        }
    };
    let Some(name) = plain_prop_name(&prop) else {
        return Ok(ExecByStmtResult::PropRegistration(
            ExecByPropRegistrationStmtResult::Failed(ExecByPropRegistrationStmtFailed::Shape(
                "by reflexive_prop: prop name must be a plain atomic name".to_string(),
            )),
        ));
    };
    let Some(definition) = runtime.def_prop_visible_in_stack(name) else {
        return Ok(ExecByStmtResult::PropRegistration(
            ExecByPropRegistrationStmtResult::Failed(
                ExecByPropRegistrationStmtFailed::PropNotDefined(name.to_string()),
            ),
        ));
    };
    let arity = definition
        .typed_parameters
        .groups
        .iter()
        .map(|g| g.params.len())
        .sum::<usize>();
    if arity != 2 {
        return Ok(ExecByStmtResult::PropRegistration(
            ExecByPropRegistrationStmtResult::Failed(
                ExecByPropRegistrationStmtFailed::WrongArity {
                    prop: prop.clone(),
                    expected: 2,
                    actual: arity,
                },
            ),
        ));
    }

    // Empty proof: rely on verify_forall_fact (ByDefinition / EqualIr, …).
    // Non-empty proof is not yet a separate local-exec path; still verify forall.
    let _ = &stmt.proof;
    let verify_state = VerifyState {
        can_use_forall_fact: true,
        can_use_rewrite: true,
        store_well_defined_fact: true,
    };
    let forall_proof = runtime.verify_forall_fact(&stmt.forall_fact, verify_state)?;
    if forall_proof.is_failed() {
        return Ok(ExecByStmtResult::PropRegistration(
            ExecByPropRegistrationStmtResult::Failed(ExecByPropRegistrationStmtFailed::Forall(
                forall_proof,
            )),
        ));
    }

    runtime
        .top_exec_env_mut()
        .prop_rewrite_properties
        .entry(prop.clone())
        .or_default()
        .push(PropRewriteProperty::Reflexive);

    Ok(ExecByStmtResult::PropRegistration(
        ExecByPropRegistrationStmtResult::Success(ExecByPropRegistrationStmtSuccess {
            prop,
            forall_proof,
        }),
    ))
}
