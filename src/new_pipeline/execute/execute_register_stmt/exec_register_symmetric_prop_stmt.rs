use super::result::{
    ExecRegisterStmtResult, ExecRegisterSymmetricPropStmtFailed,
    ExecRegisterSymmetricPropStmtResult, ExecRegisterSymmetricPropStmtSuccess,
};
use crate::new_pipeline::ast::stmt::RegisterSymmetricPropStmt;
use crate::new_pipeline::exec_env::exec_env::PropRewriteProperty;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::parse::prop_registration_shape::{
    plain_prop_name, symmetric_prop_registration_from_forall,
};
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

pub fn exec_register_symmetric_prop_stmt(
    runtime: &mut Runtime,
    stmt: &RegisterSymmetricPropStmt,
) -> RuntimeResult<ExecRegisterStmtResult> {
    let (prop, gather) = match symmetric_prop_registration_from_forall(&stmt.forall_fact) {
        Ok(v) => v,
        Err(msg) => {
            return Ok(ExecRegisterStmtResult::SymmetricProp(
                ExecRegisterSymmetricPropStmtResult::Failed(
                    ExecRegisterSymmetricPropStmtFailed::Shape(msg),
                ),
            ));
        }
    };
    let name = plain_prop_name(&prop);
    let Some(definition) = runtime.def_prop_visible_in_stack(name) else {
        return Ok(ExecRegisterStmtResult::SymmetricProp(
            ExecRegisterSymmetricPropStmtResult::Failed(
                ExecRegisterSymmetricPropStmtFailed::PropNotDefined(name.to_string()),
            ),
        ));
    };
    let arity = definition
        .typed_parameters
        .groups
        .iter()
        .map(|g| g.params.len())
        .sum::<usize>();
    if arity != gather.len() {
        return Ok(ExecRegisterStmtResult::SymmetricProp(
            ExecRegisterSymmetricPropStmtResult::Failed(
                ExecRegisterSymmetricPropStmtFailed::WrongArity {
                    prop: prop.clone(),
                    expected: gather.len(),
                    actual: arity,
                },
            ),
        ));
    }

    let verify_state = VerifyState {
        can_use_forall_fact: true,
        can_use_rewrite: true,
        store_well_defined_fact: true,
    };
    let (forall_outcome, local_env) = runtime.run_in_local_env_and_take_env(|rt| {
        let forall_proof = rt.verify_forall_fact(&stmt.forall_fact, verify_state)?;
        if forall_proof.is_failed() {
            return Ok(Err(forall_proof));
        }
        Ok(Ok(forall_proof))
    })?;
    let forall_proof = match forall_outcome {
        Ok(p) => p,
        Err(failed) => {
            return Ok(ExecRegisterStmtResult::SymmetricProp(
                ExecRegisterSymmetricPropStmtResult::Failed(
                    ExecRegisterSymmetricPropStmtFailed::Forall(failed),
                ),
            ));
        }
    };

    runtime
        .top_exec_env_mut()
        .prop_rewrite_properties
        .entry(prop.clone())
        .or_default()
        .push(PropRewriteProperty::SymmetricArgumentPermutate(vec![gather]));

    Ok(ExecRegisterStmtResult::SymmetricProp(
        ExecRegisterSymmetricPropStmtResult::Success(ExecRegisterSymmetricPropStmtSuccess {
            prop,
            forall_proof,
            local_env,
        }),
    ))
}
