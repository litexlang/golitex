use super::result::{
    ExecRegisterReflexivePropStmtFailed, ExecRegisterReflexivePropStmtResult,
    ExecRegisterReflexivePropStmtSuccess, ExecRegisterStmtResult,
};
use crate::ast::stmt::RegisterReflexivePropStmt;
use crate::exec_env::exec_env::PropRewriteProperty;
use crate::execute::execute_fact_stmt::VerifyState;
use crate::parse::prop_registration_shape::{
    plain_prop_name, reflexive_prop_name_from_forall,
};
use crate::runtime::{Runtime, RuntimeResult};

pub fn exec_register_reflexive_prop_stmt(
    runtime: &mut Runtime,
    stmt: &RegisterReflexivePropStmt,
) -> RuntimeResult<ExecRegisterStmtResult> {
    let prop = match reflexive_prop_name_from_forall(&stmt.forall_fact) {
        Ok(p) => p,
        Err(msg) => {
            return Ok(ExecRegisterStmtResult::ReflexiveProp(
                ExecRegisterReflexivePropStmtResult::Failed(
                    ExecRegisterReflexivePropStmtFailed::Shape(msg),
                ),
            ));
        }
    };
    let name = plain_prop_name(&prop);
    let Some(definition) = runtime.def_prop_visible_in_stack(name) else {
        return Ok(ExecRegisterStmtResult::ReflexiveProp(
            ExecRegisterReflexivePropStmtResult::Failed(
                ExecRegisterReflexivePropStmtFailed::PropNotDefined(name.to_string()),
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
        return Ok(ExecRegisterStmtResult::ReflexiveProp(
            ExecRegisterReflexivePropStmtResult::Failed(
                ExecRegisterReflexivePropStmtFailed::WrongArity {
                    prop: prop.clone(),
                    expected: 2,
                    actual: arity,
                },
            ),
        ));
    }

    let verify_state = VerifyState {
            can_use_builtin_rule: true,
        can_use_def_and_known_forall_and_known_strategy: true,
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
            return Ok(ExecRegisterStmtResult::ReflexiveProp(
                ExecRegisterReflexivePropStmtResult::Failed(
                    ExecRegisterReflexivePropStmtFailed::Forall(failed),
                ),
            ));
        }
    };

    runtime
        .top_exec_env_mut()
        .prop_rewrite_properties
        .entry(prop.clone())
        .or_default()
        .push(PropRewriteProperty::Reflexive);

    Ok(ExecRegisterStmtResult::ReflexiveProp(
        ExecRegisterReflexivePropStmtResult::Success(ExecRegisterReflexivePropStmtSuccess {
            prop,
            forall_proof,
            local_env,
        }),
    ))
}
