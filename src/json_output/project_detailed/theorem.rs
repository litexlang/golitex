//! Named theorem contracts and stage-specific failures for both JSON views.
use super::store::project_store_and_infer;
use super::verify::project_verify_fact;
use super::wd::{project_fact_wd_proof, project_verify_fact_wd_result};
use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_by_stmt::{
    BuiltinThmApplication, ExecByThmStmtFailed, ExecReleaseThmStmtFailed, ExecReleaseThmStmtResult,
};
use crate::json_output::helper::{bool_value, object_for, string};
use crate::knowledge_base::JsonValue;
use crate::runtime::Runtime;

pub(in crate::json_output) fn project_release_thm_failure(
    failed: &ExecReleaseThmStmtFailed,
    rt: &Runtime,
) -> JsonValue {
    use ExecReleaseThmStmtFailed::*;
    match failed {
        ThmNotFound(name) => object_for(
            rt,
            vec![
                ("phase", string("lookup")),
                ("thm_name", string(name.clone())),
                ("message", string(format!("theorem `{name}` was not found"))),
            ],
        ),
        Shape(message) | Instantiate(message) => object_for(
            rt,
            vec![
                (
                    "phase",
                    string(if matches!(failed, Shape(_)) {
                        "call_shape"
                    } else {
                        "instantiate"
                    }),
                ),
                ("message", string(message.clone())),
            ],
        ),
        BuiltinArity {
            theorem,
            expected,
            actual,
        } => object_for(
            rt,
            vec![
                ("phase", string("arity")),
                ("thm_name", string(theorem.as_str())),
                ("expected", JsonValue::Number(*expected as f64)),
                ("actual", JsonValue::Number(*actual as f64)),
                (
                    "message",
                    string(format!(
                        "builtin theorem `{theorem}` expects {expected} argument(s), got {actual}"
                    )),
                ),
            ],
        ),
        BuiltinShape { theorem, message } => object_for(
            rt,
            vec![
                ("phase", string("call_shape")),
                ("thm_name", string(theorem.as_str())),
                ("message", string(message.clone())),
            ],
        ),
        Type {
            theorem,
            fact,
            index,
            result,
        }
        | Dom {
            theorem,
            fact,
            index,
            result,
        } => object_for(
            rt,
            vec![
                (
                    "phase",
                    string(if matches!(failed, Type { .. }) {
                        "argument_type"
                    } else {
                        "premise"
                    }),
                ),
                ("thm_name", string(theorem.clone())),
                ("index", JsonValue::Number(*index as f64)),
                ("goal", string(fact.readable_string())),
                ("result", project_verify_fact(result, rt)),
            ],
        ),
        ConclusionWd {
            theorem,
            fact,
            index,
            result,
        } => object_for(
            rt,
            vec![
                ("phase", string("conclusion_well_defined")),
                ("thm_name", string(theorem.clone())),
                ("index", JsonValue::Number(*index as f64)),
                ("goal", string(fact.readable_string())),
                ("result", project_verify_fact_wd_result(result, rt)),
            ],
        ),
        FunctionDomain { theorem, result } => object_for(
            rt,
            vec![
                ("phase", string("function_domain")),
                ("thm_name", string(theorem.clone())),
                (
                    "result",
                    super::function_domain::project_function_domain_failure(result, rt),
                ),
            ],
        ),
        Store {
            theorem,
            index,
            message,
        } => object_for(
            rt,
            vec![
                ("phase", string("store")),
                ("thm_name", string(theorem.clone())),
                ("index", JsonValue::Number(*index as f64)),
                ("message", string(message.clone())),
            ],
        ),
    }
}
pub(in crate::json_output) fn project_by_thm_failure(
    failed: &ExecByThmStmtFailed,
    rt: &Runtime,
) -> JsonValue {
    match failed {
        ExecByThmStmtFailed::Release(failed) => project_release_thm_failure(failed, rt),
        ExecByThmStmtFailed::NotReturned { theorem, fact, conclusions } => object_for(rt, vec![
            ("phase", string("selected_fact")), ("reason", string("not_returned")),
            ("thm_name", string(theorem.clone())), ("goal", string(fact.readable_string())),
            ("returned_conclusions", JsonValue::Array(conclusions.iter().map(|f| string(f.readable_string())).collect())),
            ("message", string("Selected fact must match a directly returned atomic conclusion; independent verification and combining conclusions are not allowed")),
        ]),
        ExecByThmStmtFailed::Selected { theorem, fact, result } => object_for(rt, vec![("phase", string("selected_fact")), ("thm_name", string(theorem.clone())), ("goal", string(fact.readable_string())), ("result", project_verify_fact(result, rt))]),
        ExecByThmStmtFailed::Store { theorem, message } => object_for(rt, vec![("phase", string("store")), ("thm_name", string(theorem.clone())), ("message", string(message.clone()))]),
    }
}
pub(super) fn project_builtin_application(
    application: &Option<BuiltinThmApplication>,
    rt: &Runtime,
) -> JsonValue {
    let Some(p) = application else {
        return JsonValue::Null;
    };
    project_builtin_application_value(p, rt)
}

pub(super) fn project_builtin_application_value(
    p: &BuiltinThmApplication,
    rt: &Runtime,
) -> JsonValue {
    let provenance = if matches!(
        p.theorem,
        BuiltinTheoremId::IndexCartesianNonemptyByChoiceFromFamily
            | BuiltinTheoremId::IndexCartesianNonemptyByChoiceFromPointwise
    ) {
        "axiom_of_choice"
    } else {
        "builtin_theorem"
    };
    object_for(
        rt,
        vec![
            ("theorem", string(p.theorem.as_str())),
            (
                "arguments",
                JsonValue::Array(
                    p.arguments
                        .iter()
                        .map(|x| string(x.readable_string()))
                        .collect(),
                ),
            ),
            (
                "requirements",
                JsonValue::Array(
                    p.requirements
                        .iter()
                        .map(|x| string(x.readable_string()))
                        .collect(),
                ),
            ),
            (
                "conclusions",
                JsonValue::Array(
                    p.conclusions
                        .iter()
                        .map(|x| string(x.readable_string()))
                        .collect(),
                ),
            ),
            ("provenance", string(provenance)),
        ],
    )
}
pub(super) fn project_conclusions_wd(
    proofs: &[crate::execute::execute_fact_stmt::FactWellDefinedProof],
    rt: &Runtime,
) -> JsonValue {
    JsonValue::Array(
        proofs
            .iter()
            .map(|proof| project_fact_wd_proof(proof, rt))
            .collect(),
    )
}
pub(super) fn project_release_thm(result: &ExecReleaseThmStmtResult, rt: &Runtime) -> JsonValue {
    match result {
        ExecReleaseThmStmtResult::Success(s) => object_for(
            rt,
            vec![
                ("success", bool_value(true)),
                ("kind", string("release_thm")),
                ("thm_name", string(s.call.name.local_name().to_string())),
                ("call", project_theorem_call(&s.call, rt)),
                ("builtin", project_builtin_application(&s.builtin, rt)),
                (
                    "type_proofs",
                    super::store::project_verify_facts(&s.type_proofs, rt),
                ),
                (
                    "function_domain",
                    s.function_domain
                        .as_ref()
                        .map(|p| project_builtin_function_domain(p, rt))
                        .unwrap_or(JsonValue::Null),
                ),
                (
                    "dom_proofs",
                    super::store::project_verify_facts(&s.dom_proofs, rt),
                ),
                (
                    "conclusions_wd",
                    project_conclusions_wd(&s.conclusions_wd, rt),
                ),
                (
                    "stored",
                    JsonValue::Array(
                        s.stored
                            .iter()
                            .map(|x| project_store_and_infer(x, rt))
                            .collect(),
                    ),
                ),
            ],
        ),
        ExecReleaseThmStmtResult::Failed(f) => object_for(
            rt,
            vec![
                ("success", bool_value(false)),
                ("kind", string("release_thm")),
                ("failure", project_release_thm_failure(f, rt)),
            ],
        ),
    }
}

pub(super) fn project_theorem_call(
    call: &crate::ast::stmt::TheoremCall,
    rt: &Runtime,
) -> JsonValue {
    use crate::ast::names::AtomicName;
    use crate::ast::stmt::TheoremCallArguments;
    let name = match &call.name {
        AtomicName::Plain { name } => object_for(
            rt,
            vec![("type", string("plain")), ("name", string(name.clone()))],
        ),
        AtomicName::WithExportFileId {
            export_file_id,
            name,
        } => object_for(
            rt,
            vec![
                ("type", string("export")),
                ("export_file_id", JsonValue::Number(*export_file_id as f64)),
                ("name", string(name.clone())),
            ],
        ),
        AtomicName::WithModAndExportFileId {
            global_mod_id,
            export_file_id,
            name,
        } => object_for(
            rt,
            vec![
                ("type", string("module_export")),
                ("global_mod_id", JsonValue::Number(*global_mod_id as f64)),
                ("export_file_id", JsonValue::Number(*export_file_id as f64)),
                ("name", string(name.clone())),
            ],
        ),
    };
    let arguments = match &call.arguments {
        TheoremCallArguments::Bare => JsonValue::Null,
        TheoremCallArguments::Parenthesized(args) => JsonValue::Array(
            args.iter()
                .map(|obj| string(obj.readable_string()))
                .collect(),
        ),
    };
    object_for(rt, vec![("name", name), ("arguments", arguments)])
}

pub(in crate::json_output) fn project_def_thm_failure(
    failed: &crate::execute::ExecDefThmStmtFailed,
    rt: &Runtime,
) -> JsonValue {
    use crate::execute::ExecDefThmStmtFailed::*;
    match failed {
        GoalUnsupported(text) => object_for(
            rt,
            vec![
                ("phase", string("goal_unsupported")),
                ("message", string(text.clone())),
            ],
        ),
        NameClash(text) | Introduce(text) | Store(text) => object_for(
            rt,
            vec![
                (
                    "phase",
                    string(match failed {
                        NameClash(_) => "name_clash",
                        Introduce(_) => "introduce",
                        _ => "store",
                    }),
                ),
                ("message", string(text.clone())),
            ],
        ),
        GoalWd(result) => object_for(
            rt,
            vec![
                ("phase", string("goal_well_defined")),
                ("result", project_verify_fact_wd_result(result, rt)),
            ],
        ),
        ProofBody(f) => object_for(
            rt,
            vec![
                ("phase", string("proof_body")),
                ("index", JsonValue::Number(f.step_index as f64)),
                ("result", super::stmt::project_stmt_detailed(&f.result, rt)),
            ],
        ),
        Conclusion { index, result } => object_for(
            rt,
            vec![
                ("phase", string("conclusion")),
                ("index", JsonValue::Number(*index as f64)),
                ("result", project_verify_fact(result, rt)),
            ],
        ),
    }
}

pub(super) fn project_builtin_function_domain(
    proof: &crate::execute::execute_by_stmt::BuiltinFunctionDomainProof,
    rt: &Runtime,
) -> JsonValue {
    use crate::execute::execute_by_stmt::BuiltinFunctionDomainProof;
    match proof {
        BuiltinFunctionDomainProof::Membership(proof) => {
            super::function_domain::project_function_domain(proof, rt)
        }
        BuiltinFunctionDomainProof::TupleEquality { left, right } => object_for(
            rt,
            vec![
                ("type", string("tuple_exact_domains")),
                (
                    "left",
                    super::function_domain::project_function_domain(left, rt),
                ),
                (
                    "right",
                    super::function_domain::project_function_domain(right, rt),
                ),
            ],
        ),
    }
}
