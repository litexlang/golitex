//! Preserve the checked stage and child reason of a failed template definition.

use super::verify::{project_exist_failed, project_verify_fact};
use super::wd::project_verify_obj_wd;
use super::wd_failure::project_fact_wd_failure;
use crate::execute::execute_def_template_stmt::ExecDefTemplateStmtFailed;
use crate::execute::{
    ExecHaveByReplacementAxiomStmtFailed, ExecHaveFnByForallExistUniqueStmtFailed,
    ExecHaveFnEqualStmtFailed, ExecHaveObjByExistFactsStmtFailed, ExecHaveObjEqualStmtFailed,
    ExecHaveObjInNonemptySetStmtFailed, ExecObtainObjFromAtomicFactStmtFailed,
    ExecObtainObjFromExistFactStmtFailed, ExecTrustHaveStmtFailed, FailToReleaseOneStructLayer,
};
use crate::json_output::helper::{object_for, string};
use crate::knowledge_base::JsonValue;
use crate::runtime::Runtime;

pub(in crate::json_output) fn project_template_failure(
    failed: &ExecDefTemplateStmtFailed,
    runtime: &Runtime,
) -> JsonValue {
    let (phase, failure) = match failed {
        ExecDefTemplateStmtFailed::ParamType(wd) => {
            ("parameter_type", project_verify_obj_wd(wd, runtime))
        }
        ExecDefTemplateStmtFailed::AutoOpenStructLayer(f) => {
            ("auto_open_struct_layer", project_open_failure(f, runtime))
        }
        ExecDefTemplateStmtFailed::DomainFact(wd) => (
            "domain_fact_well_defined",
            project_fact_wd_failure(wd, runtime),
        ),
        ExecDefTemplateStmtFailed::BodyHaveObjInNonemptySet(f) => {
            ("body_have_in_nonempty", project_have_in_failure(f, runtime))
        }
        ExecDefTemplateStmtFailed::BodyHaveObjEqual(f) => {
            ("body_have_equal", project_have_equal_failure(f, runtime))
        }
        ExecDefTemplateStmtFailed::BodyHaveObjByExistFacts(f) => {
            let ExecHaveObjByExistFactsStmtFailed::Exist(exist) = f;
            (
                "body_have_by_exist",
                project_exist_failed("exist", exist, runtime),
            )
        }
        ExecDefTemplateStmtFailed::BodyHaveByReplacementAxiom(f) => (
            "body_have_by_replacement",
            project_replacement_failure(f, runtime),
        ),
        ExecDefTemplateStmtFailed::BodyObtainObjFromExistFact(f) => (
            "body_obtain_from_exist",
            project_obtain_exist_failure(f, runtime),
        ),
        ExecDefTemplateStmtFailed::BodyObtainObjFromAtomicFact(f) => (
            "body_obtain_from_atomic",
            project_obtain_atomic_failure(f, runtime),
        ),
        ExecDefTemplateStmtFailed::BodyHaveFnEqual(f) => {
            let (phase, wd) = match f {
                ExecHaveFnEqualStmtFailed::AnonymousFnWellDefined(wd) => {
                    ("anonymous_fn_well_defined", wd)
                }
                ExecHaveFnEqualStmtFailed::FnSetWellDefined(wd) => ("fn_set_well_defined", wd),
            };
            (
                "body_have_fn_equal",
                node(runtime, phase, project_verify_obj_wd(wd, runtime)),
            )
        }
        ExecDefTemplateStmtFailed::BodyHaveFnEqualCaseByCase(f) => (
            "body_have_fn_cases",
            super::stmt::project_cases_definition_failure(f, runtime),
        ),
        ExecDefTemplateStmtFailed::BodyHaveFnByForallExistUnique(f) => (
            "body_have_fn_forall_exist_unique",
            project_unique_fn_failure(f, runtime),
        ),
        ExecDefTemplateStmtFailed::BodyHaveFnByInduc(f) => (
            "body_have_fn_induc",
            super::induction::project_induc_definition_failure(f, runtime),
        ),
        ExecDefTemplateStmtFailed::BodyTrustHave(f) => {
            ("body_trust_have", project_trust_have_failure(f, runtime))
        }
        ExecDefTemplateStmtFailed::UnsupportedBody(message) => {
            ("unsupported_body", message_json(runtime, message))
        }
    };
    node(runtime, phase, failure)
}

fn node(runtime: &Runtime, phase: &str, failure: JsonValue) -> JsonValue {
    object_for(
        runtime,
        vec![("phase", string(phase)), ("failure", failure)],
    )
}

fn message_json(runtime: &Runtime, message: &str) -> JsonValue {
    object_for(runtime, vec![("message", string(message))])
}

fn project_open_failure(f: &FailToReleaseOneStructLayer, runtime: &Runtime) -> JsonValue {
    object_for(
        runtime,
        vec![
            ("obj", string(f.obj.readable_string())),
            ("struct_obj", string(f.struct_obj.readable_string())),
            ("reason", string(&f.reason)),
        ],
    )
}

fn project_have_in_failure(f: &ExecHaveObjInNonemptySetStmtFailed, runtime: &Runtime) -> JsonValue {
    let (phase, failure) = match f {
        ExecHaveObjInNonemptySetStmtFailed::ParamType(wd) => {
            ("parameter_type", project_verify_obj_wd(wd, runtime))
        }
        ExecHaveObjInNonemptySetStmtFailed::NonemptyCheck(v) => {
            ("nonempty_check", project_verify_fact(v, runtime))
        }
        ExecHaveObjInNonemptySetStmtFailed::AutoOpenStructLayer(f) => {
            ("auto_open_struct_layer", project_open_failure(f, runtime))
        }
    };
    node(runtime, phase, failure)
}

fn project_have_equal_failure(f: &ExecHaveObjEqualStmtFailed, runtime: &Runtime) -> JsonValue {
    let (phase, failure) = match f {
        ExecHaveObjEqualStmtFailed::ParamCountMismatch => (
            "parameter_count",
            message_json(runtime, "parameter and value counts differ"),
        ),
        ExecHaveObjEqualStmtFailed::ParamType(wd) => {
            ("parameter_type", project_verify_obj_wd(wd, runtime))
        }
        ExecHaveObjEqualStmtFailed::EqualToWellDefined(wd) => {
            ("equal_to_well_defined", project_verify_obj_wd(wd, runtime))
        }
        ExecHaveObjEqualStmtFailed::Membership(v) => {
            ("membership", project_verify_fact(v, runtime))
        }
        ExecHaveObjEqualStmtFailed::AutoOpenStructLayer(f) => {
            ("auto_open_struct_layer", project_open_failure(f, runtime))
        }
    };
    node(runtime, phase, failure)
}

fn project_replacement_failure(
    f: &ExecHaveByReplacementAxiomStmtFailed,
    runtime: &Runtime,
) -> JsonValue {
    let (phase, failure) = match f {
        ExecHaveByReplacementAxiomStmtFailed::PropArity(message) => {
            ("prop_arity", message_json(runtime, message))
        }
        ExecHaveByReplacementAxiomStmtFailed::SourceWd(wd) => {
            ("source_well_defined", project_verify_obj_wd(wd, runtime))
        }
        ExecHaveByReplacementAxiomStmtFailed::UniquenessMissing(message) => {
            ("uniqueness", message_json(runtime, message))
        }
        ExecHaveByReplacementAxiomStmtFailed::Define(message) => {
            ("define", message_json(runtime, message))
        }
    };
    node(runtime, phase, failure)
}

fn project_obtain_exist_failure(
    f: &ExecObtainObjFromExistFactStmtFailed,
    runtime: &Runtime,
) -> JsonValue {
    let (phase, failure) = match f {
        ExecObtainObjFromExistFactStmtFailed::ArityMismatch { expected, got } => (
            "arity",
            object_for(
                runtime,
                vec![
                    ("expected", JsonValue::Number(*expected as f64)),
                    ("actual", JsonValue::Number(*got as f64)),
                ],
            ),
        ),
        ExecObtainObjFromExistFactStmtFailed::NotExistSource => (
            "source",
            message_json(runtime, "source is not an existential fact"),
        ),
        ExecObtainObjFromExistFactStmtFailed::Exist(exist) => {
            ("exist", project_exist_failed("exist", exist, runtime))
        }
    };
    node(runtime, phase, failure)
}

fn project_obtain_atomic_failure(
    f: &ExecObtainObjFromAtomicFactStmtFailed,
    runtime: &Runtime,
) -> JsonValue {
    let (phase, failure) = match f {
        ExecObtainObjFromAtomicFactStmtFailed::AbstractProp => (
            "abstract_prop",
            message_json(
                runtime,
                "abstract proposition has no existential definition",
            ),
        ),
        ExecObtainObjFromAtomicFactStmtFailed::PropNotFound => {
            ("prop", message_json(runtime, "proposition is not defined"))
        }
        ExecObtainObjFromAtomicFactStmtFailed::BadDefinition(message) => {
            ("definition", message_json(runtime, message))
        }
        ExecObtainObjFromAtomicFactStmtFailed::AtomicVerifyFailed(v) => {
            ("atomic", project_verify_fact(v, runtime))
        }
        ExecObtainObjFromAtomicFactStmtFailed::Instantiate(message) => {
            ("instantiate", message_json(runtime, message))
        }
        ExecObtainObjFromAtomicFactStmtFailed::Apply(f) => {
            ("apply", project_obtain_exist_failure(f, runtime))
        }
    };
    node(runtime, phase, failure)
}

fn project_unique_fn_failure(
    f: &ExecHaveFnByForallExistUniqueStmtFailed,
    runtime: &Runtime,
) -> JsonValue {
    let (phase, failure) = match f {
        ExecHaveFnByForallExistUniqueStmtFailed::SourceForall(v) => {
            ("source_forall", project_verify_fact(v, runtime))
        }
        ExecHaveFnByForallExistUniqueStmtFailed::FnSetWellDefined(wd) => {
            ("fn_set_well_defined", project_verify_obj_wd(wd, runtime))
        }
        ExecHaveFnByForallExistUniqueStmtFailed::PropertyWellDefined(wd) => (
            "property_well_defined",
            project_fact_wd_failure(wd, runtime),
        ),
    };
    node(runtime, phase, failure)
}

fn project_trust_have_failure(f: &ExecTrustHaveStmtFailed, runtime: &Runtime) -> JsonValue {
    let (phase, failure) = match f {
        ExecTrustHaveStmtFailed::ParamType(wd) => {
            ("parameter_type", project_verify_obj_wd(wd, runtime))
        }
        ExecTrustHaveStmtFailed::AutoOpenStructLayer(f) => {
            ("auto_open_struct_layer", project_open_failure(f, runtime))
        }
        ExecTrustHaveStmtFailed::BodyFactWellDefined(wd) => (
            "body_fact_well_defined",
            project_fact_wd_failure(wd, runtime),
        ),
    };
    node(runtime, phase, failure)
}
