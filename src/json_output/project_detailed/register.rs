//! Preserve existing registered-law verification; omit only the retained local env.

use super::verify::project_verify_fact;
use crate::execute::execute_register_stmt::{
    ExecRegisterReflexivePropStmtFailed as RF, ExecRegisterReflexivePropStmtResult as R,
    ExecRegisterStmtResult, ExecRegisterSymmetricPropStmtFailed as SF,
    ExecRegisterSymmetricPropStmtResult as S, ExecRegisterTransitivePropStmtFailed as TF,
    ExecRegisterTransitivePropStmtResult as T,
};
use crate::json_output::helper::{bool_value, object_for, string};
use crate::knowledge_base::JsonValue;
use crate::runtime::Runtime;

pub(super) fn project_register(result: &ExecRegisterStmtResult, runtime: &Runtime) -> JsonValue {
    let (property, success, payload) = match result {
        ExecRegisterStmtResult::ReflexiveProp(r) => match r {
            R::Success(p) => ("reflexive", true, vec![
                ("prop", string(p.prop.to_string())),
                ("forall_proof", project_verify_fact(&p.forall_proof, runtime)),
            ]),
            R::Failed(f) => ("reflexive", false, match f {
                RF::Shape(message) => vec![("phase", string("shape")), ("message", string(message))],
                RF::PropNotDefined(prop) => vec![("phase", string("prop_not_defined")), ("prop", string(prop))],
                RF::WrongArity { prop, expected, actual } => vec![
                    ("phase", string("wrong_arity")), ("prop", string(prop.to_string())),
                    ("expected", JsonValue::Number(*expected as f64)), ("actual", JsonValue::Number(*actual as f64)),
                ],
                RF::Forall(proof) => vec![("phase", string("forall")), ("forall_proof", project_verify_fact(proof, runtime))],
            }),
        },
        ExecRegisterStmtResult::SymmetricProp(r) => match r {
            S::Success(p) => ("symmetric", true, vec![
                ("prop", string(p.prop.to_string())),
                ("forall_proof", project_verify_fact(&p.forall_proof, runtime)),
            ]),
            S::Failed(f) => ("symmetric", false, match f {
                SF::Shape(message) => vec![("phase", string("shape")), ("message", string(message))],
                SF::PropNotDefined(prop) => vec![("phase", string("prop_not_defined")), ("prop", string(prop))],
                SF::WrongArity { prop, expected, actual } => vec![
                    ("phase", string("wrong_arity")), ("prop", string(prop.to_string())),
                    ("expected", JsonValue::Number(*expected as f64)), ("actual", JsonValue::Number(*actual as f64)),
                ],
                SF::Forall(proof) => vec![("phase", string("forall")), ("forall_proof", project_verify_fact(proof, runtime))],
            }),
        },
        ExecRegisterStmtResult::TransitiveProp(r) => match r {
            T::Success(p) => ("transitive", true, vec![
                ("prop", string(p.prop.to_string())),
                ("forall_proof", project_verify_fact(&p.forall_proof, runtime)),
            ]),
            T::Failed(f) => ("transitive", false, match f {
                TF::Shape(message) => vec![("phase", string("shape")), ("message", string(message))],
                TF::PropNotDefined(prop) => vec![("phase", string("prop_not_defined")), ("prop", string(prop))],
                TF::WrongArity { prop, expected, actual } => vec![
                    ("phase", string("wrong_arity")), ("prop", string(prop.to_string())),
                    ("expected", JsonValue::Number(*expected as f64)), ("actual", JsonValue::Number(*actual as f64)),
                ],
                TF::Forall(proof) => vec![("phase", string("forall")), ("forall_proof", project_verify_fact(proof, runtime))],
            }),
        },
    };
    let mut fields = vec![("success", bool_value(success)), ("kind", string("register")), ("property", string(property))];
    if success {
        fields.extend(payload);
    } else {
        fields.push(("failure", object_for(runtime, payload)));
    }
    object_for(runtime, fields)
}
