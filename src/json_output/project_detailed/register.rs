//! Registered-law evidence and typed failure diagnostics shared by both views.
use crate::prelude::*;

pub(in crate::json_output) fn project_register(
    result: &crate::execute::execute_register_stmt::ExecRegisterStmtResult,
    runtime: &Runtime,
) -> JsonValue {
    use crate::execute::execute_register_stmt::*;
    use crate::json_output::helper::{
        inherit_failure_field, object_for, statement_result_value, string,
    };
    let (property, proof) = match result {
        ExecRegisterStmtResult::ReflexiveProp(r) => (
            "reflexive",
            match r {
                ExecRegisterReflexivePropStmtResult::Success(p) => Some((&p.prop, &p.forall_proof)),
                ExecRegisterReflexivePropStmtResult::Failed(_) => None,
            },
        ),
        ExecRegisterStmtResult::SymmetricProp(r) => (
            "symmetric",
            match r {
                ExecRegisterSymmetricPropStmtResult::Success(p) => Some((&p.prop, &p.forall_proof)),
                ExecRegisterSymmetricPropStmtResult::Failed(_) => None,
            },
        ),
        ExecRegisterStmtResult::TransitiveProp(r) => (
            "transitive",
            match r {
                ExecRegisterTransitivePropStmtResult::Success(p) => {
                    Some((&p.prop, &p.forall_proof))
                }
                ExecRegisterTransitivePropStmtResult::Failed(_) => None,
            },
        ),
    };
    let mut fields = vec![
        ("statement_result", statement_result_value(proof.is_some())),
        ("kind", string("register")),
        ("property", string(property)),
    ];
    match proof {
        Some((prop, proof)) => {
            fields.push(("prop", string(prop.to_string())));
            fields.push((
                "forall_proof",
                super::verify::project_verify_fact(proof, runtime),
            ));
        }
        None => fields.push(("failure", project_register_failure(result, runtime))),
    }
    inherit_failure_field(runtime, object_for(runtime, fields), "failure")
}

pub(in crate::json_output) fn project_register_failure(
    result: &crate::execute::execute_register_stmt::ExecRegisterStmtResult,
    runtime: &Runtime,
) -> JsonValue {
    use crate::execute::execute_register_stmt::*;
    use crate::json_output::failure_kind::FailureKind;
    use crate::json_output::helper::{
        inherit_failure_field, object_for, string, with_failure_diagnostic,
    };
    let (kind, fields) = match result {
        ExecRegisterStmtResult::ReflexiveProp(r) => match r {
            ExecRegisterReflexivePropStmtResult::Success(_) => {
                unreachable!("failure projection requires a failed registration")
            }
            ExecRegisterReflexivePropStmtResult::Failed(f) => match f {
                ExecRegisterReflexivePropStmtFailed::Shape(message) => (
                    FailureKind::Unsupported,
                    vec![("phase", string("shape")), ("message", string(message))],
                ),
                ExecRegisterReflexivePropStmtFailed::PropNotDefined(prop) => (
                    FailureKind::NameNotFound,
                    vec![
                        ("phase", string("prop_not_defined")),
                        ("prop", string(prop)),
                    ],
                ),
                ExecRegisterReflexivePropStmtFailed::WrongArity {
                    prop,
                    expected,
                    actual,
                } => (
                    FailureKind::Arity,
                    vec![
                        ("phase", string("wrong_arity")),
                        ("prop", string(prop.to_string())),
                        ("expected", JsonValue::Number(*expected as f64)),
                        ("actual", JsonValue::Number(*actual as f64)),
                    ],
                ),
                ExecRegisterReflexivePropStmtFailed::Forall(proof) => (
                    FailureKind::for_verification(proof),
                    vec![
                        ("phase", string("forall")),
                        (
                            "forall_proof",
                            super::verify::project_verify_fact(proof, runtime),
                        ),
                    ],
                ),
            },
        },
        ExecRegisterStmtResult::SymmetricProp(r) => match r {
            ExecRegisterSymmetricPropStmtResult::Success(_) => {
                unreachable!("failure projection requires a failed registration")
            }
            ExecRegisterSymmetricPropStmtResult::Failed(f) => match f {
                ExecRegisterSymmetricPropStmtFailed::Shape(message) => (
                    FailureKind::Unsupported,
                    vec![("phase", string("shape")), ("message", string(message))],
                ),
                ExecRegisterSymmetricPropStmtFailed::PropNotDefined(prop) => (
                    FailureKind::NameNotFound,
                    vec![
                        ("phase", string("prop_not_defined")),
                        ("prop", string(prop)),
                    ],
                ),
                ExecRegisterSymmetricPropStmtFailed::WrongArity {
                    prop,
                    expected,
                    actual,
                } => (
                    FailureKind::Arity,
                    vec![
                        ("phase", string("wrong_arity")),
                        ("prop", string(prop.to_string())),
                        ("expected", JsonValue::Number(*expected as f64)),
                        ("actual", JsonValue::Number(*actual as f64)),
                    ],
                ),
                ExecRegisterSymmetricPropStmtFailed::Forall(proof) => (
                    FailureKind::for_verification(proof),
                    vec![
                        ("phase", string("forall")),
                        (
                            "forall_proof",
                            super::verify::project_verify_fact(proof, runtime),
                        ),
                    ],
                ),
            },
        },
        ExecRegisterStmtResult::TransitiveProp(r) => match r {
            ExecRegisterTransitivePropStmtResult::Success(_) => {
                unreachable!("failure projection requires a failed registration")
            }
            ExecRegisterTransitivePropStmtResult::Failed(f) => match f {
                ExecRegisterTransitivePropStmtFailed::Shape(message) => (
                    FailureKind::Unsupported,
                    vec![("phase", string("shape")), ("message", string(message))],
                ),
                ExecRegisterTransitivePropStmtFailed::PropNotDefined(prop) => (
                    FailureKind::NameNotFound,
                    vec![
                        ("phase", string("prop_not_defined")),
                        ("prop", string(prop)),
                    ],
                ),
                ExecRegisterTransitivePropStmtFailed::WrongArity {
                    prop,
                    expected,
                    actual,
                } => (
                    FailureKind::Arity,
                    vec![
                        ("phase", string("wrong_arity")),
                        ("prop", string(prop.to_string())),
                        ("expected", JsonValue::Number(*expected as f64)),
                        ("actual", JsonValue::Number(*actual as f64)),
                    ],
                ),
                ExecRegisterTransitivePropStmtFailed::Forall(proof) => (
                    FailureKind::for_verification(proof),
                    vec![
                        ("phase", string("forall")),
                        (
                            "forall_proof",
                            super::verify::project_verify_fact(proof, runtime),
                        ),
                    ],
                ),
            },
        },
    };
    let projected = inherit_failure_field(runtime, object_for(runtime, fields), "forall_proof");
    with_failure_diagnostic(runtime, projected, kind, vec![])
}
