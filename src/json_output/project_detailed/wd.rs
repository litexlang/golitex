//! Object / fact well-definedness projection for Detailed output.

use super::wd_by_def::project_obj_wd_by_def;
use crate::execute::ParamTypeWellDefinedProof;
use crate::execute::execute_fact_stmt::well_defined_results::{
    FactWellDefinedProof, ObjWellDefinedProof, VerifyObjWellDefinedResult,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::AtomicFactWellDefinedProof;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::well_defined_result::EqualFactWellDefinedProof;
use crate::execute::execute_fact_stmt::verify_exist_shaped_fact::ExistShapedFactWellDefinedProof;
use crate::execute::execute_fact_stmt::verify_forall_fact::ForallFactWellDefinedProof;
use crate::execute::execute_fact_stmt::verify_forall_fact_with_iff::ForallFactWithIffWellDefinedProof;
use crate::execute::execute_fact_stmt::verify_not_forall_fact::NotForallFactWellDefinedProof;
use crate::execute::execute_fact_stmt::verify_or_fact::OrFactWellDefinedProof;
use crate::json_output::helper::{object_for, string};
use crate::knowledge_base::JsonValue;
use crate::runtime::Runtime;

pub(super) fn project_obj_wd_proof(proof: &ObjWellDefinedProof, runtime: &Runtime) -> JsonValue {
    match proof {
        ObjWellDefinedProof::ByKnown { obj, wd_id } => object_for(runtime, vec![
            ("type", string("by_known")),
            ("obj", string(obj.readable_string())),
            ("wd_id", string(wd_id.to_string())),
        ]),
        ObjWellDefinedProof::ByDef { obj, proof } => project_obj_wd_by_def(obj, proof, runtime),
    }
}

pub(in crate::json_output) fn project_verify_obj_wd(
    result: &VerifyObjWellDefinedResult,
    runtime: &Runtime,
) -> JsonValue {
    match result {
        VerifyObjWellDefinedResult::Success(proof) => object_for(runtime, vec![
            ("success", JsonValue::Bool(true)),
            ("proof", project_obj_wd_proof(proof, runtime)),
        ]),
        VerifyObjWellDefinedResult::Failed { obj, reason: f } => object_for(runtime, vec![
            ("success", JsonValue::Bool(false)),
            ("obj", string(obj.readable_string())),
            ("phase", string("well_defined")),
            ("failure", super::wd_failure::project_obj_wd_failure(f, runtime)),
        ]),
    }
}

pub(super) fn project_atomic_wd_proof(
    proof: &AtomicFactWellDefinedProof,
    runtime: &Runtime,
) -> JsonValue {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::PredicateSignatureWellDefinedProof;
    let signature = match &proof.predicate_signature {
        PredicateSignatureWellDefinedProof::Builtin => object_for(runtime, vec![("type", string("builtin"))]),
        PredicateSignatureWellDefinedProof::Prop { predicate, arity } => object_for(runtime, vec![
            ("type", string("prop")), ("predicate", string(predicate.display_string())),
            ("arity", JsonValue::Number(*arity as f64)),
        ]),
        PredicateSignatureWellDefinedProof::AbstractProp { predicate, arity } => object_for(runtime, vec![
            ("type", string("abstract_prop")), ("predicate", string(predicate.display_string())),
            ("arity", JsonValue::Number(*arity as f64)),
        ]),
    };
    object_for(runtime, vec![(
        "well_defined_of_each_parameter",
        JsonValue::Array(
            proof
                .well_defined_of_each_parameter
                .iter()
                .map(|p| project_obj_wd_proof(p, runtime))
                .collect(),
        ),
    ), ("predicate_signature", signature),
    ("predicate_domain", JsonValue::Array(proof.predicate_domain.iter().map(|p|
        object_for(runtime, vec![
            ("requirement", string(p.requirement.readable_string())),
            ("verify", super::verify::project_verify_fact(&p.result, runtime)),
        ])).collect()))])
}

pub(super) fn project_equal_wd_proof(
    proof: &EqualFactWellDefinedProof,
    runtime: &Runtime,
) -> JsonValue {
    object_for(runtime, vec![
        ("left", project_obj_wd_proof(&proof.left, runtime)),
        ("right", project_obj_wd_proof(&proof.right, runtime)),
    ])
}

pub(super) fn project_param_type_wd(
    proof: &ParamTypeWellDefinedProof,
    runtime: &Runtime,
) -> JsonValue {
    match proof {
        ParamTypeWellDefinedProof::Set => object_for(runtime, vec![("type", string("set"))]),
        ParamTypeWellDefinedProof::NonemptySet => object_for(runtime, vec![("type", string("nonempty_set"))]),
        ParamTypeWellDefinedProof::FiniteSet => object_for(runtime, vec![("type", string("finite_set"))]),
        ParamTypeWellDefinedProof::Obj(wd) => object_for(runtime, vec![
            ("type", string("obj")),
            ("well_defined", project_verify_obj_wd(wd, runtime)),
        ]),
    }
}

pub(super) fn project_verify_fact_wd_result(
    result: &crate::execute::execute_fact_stmt::VerifyFactWellDefinedResult,
    runtime: &Runtime,
) -> JsonValue {
    match result {
        crate::execute::execute_fact_stmt::VerifyFactWellDefinedResult::Success(proof) => {
            object_for(runtime, vec![
                ("success", JsonValue::Bool(true)),
                ("proof", project_fact_wd_proof(proof, runtime)),
            ])
        }
        crate::execute::execute_fact_stmt::VerifyFactWellDefinedResult::Failed(f) => object_for(runtime, vec![
            ("success", JsonValue::Bool(false)),
            ("phase", string("well_defined")),
            ("failure", super::wd_failure::project_fact_wd_failure(f, runtime)),
        ]),
    }
}

pub(super) fn project_fact_wd_proof(proof: &FactWellDefinedProof, runtime: &Runtime) -> JsonValue {
    match proof {
        FactWellDefinedProof::Equality(p) => object_for(runtime, vec![
            ("type", string("equality")),
            ("proof", project_equal_wd_proof(p, runtime)),
        ]),
        FactWellDefinedProof::AtomicExceptEquality(p) => object_for(runtime, vec![
            ("type", string("atomic_except_equality")),
            ("proof", project_atomic_wd_proof(p, runtime)),
        ]),
        FactWellDefinedProof::AndFact { components } => object_for(runtime, vec![
            ("type", string("and")),
            (
                "components",
                JsonValue::Array(
                    components
                        .iter()
                        .map(|c| project_atomic_wd_proof(c, runtime))
                        .collect(),
                ),
            ),
        ]),
        FactWellDefinedProof::ChainFact { adjacent } => object_for(runtime, vec![
            ("type", string("chain")),
            (
                "adjacent",
                JsonValue::Array(
                    adjacent
                        .iter()
                        .map(|c| project_atomic_wd_proof(c, runtime))
                        .collect(),
                ),
            ),
        ]),
        FactWellDefinedProof::OrFact(p) => project_or_wd_proof(p, runtime),
        FactWellDefinedProof::ExistFact(p) => project_exist_wd_proof(p, runtime),
        FactWellDefinedProof::ForallFact(p) => project_forall_wd(p, runtime),
        FactWellDefinedProof::ForallFactWithIff(p) => project_forall_iff_wd(p, runtime),
        FactWellDefinedProof::NotForall(p) => project_not_forall_wd(p, runtime),
    }
}

pub(super) fn project_or_wd_proof(proof: &OrFactWellDefinedProof, runtime: &Runtime) -> JsonValue {
    object_for(runtime, vec![
        ("type", string("or")),
        (
            "branches",
            JsonValue::Array(
                proof
                    .branches
                    .iter()
                    .map(|c| project_fact_wd_proof(c, runtime))
                    .collect(),
            ),
        ),
    ])
}

pub(super) fn project_exist_wd_proof(
    proof: &ExistShapedFactWellDefinedProof,
    runtime: &Runtime,
) -> JsonValue {
    object_for(runtime, vec![
        ("type", string("exist_shaped")),
        (
            "param_type_well_defined",
            JsonValue::Array(
                proof
                    .param_type_well_defined
                    .iter()
                    .map(|p| project_param_type_wd(p, runtime))
                    .collect(),
            ),
        ),
        (
            "body",
            JsonValue::Array(
                proof
                    .body
                    .iter()
                    .map(|f| project_fact_wd_proof(f, runtime))
                    .collect(),
            ),
        ),
            ])
}

pub(super) fn project_forall_wd(proof: &ForallFactWellDefinedProof, runtime: &Runtime) -> JsonValue {
    object_for(runtime, vec![
        ("type", string("forall")),
        (
            "param_type_well_defined",
            JsonValue::Array(
                proof
                    .param_type_well_defined
                    .iter()
                    .map(|p| project_param_type_wd(p, runtime))
                    .collect(),
            ),
        ),
        (
            "dom",
            JsonValue::Array(
                proof
                    .dom
                    .iter()
                    .map(|f| project_fact_wd_proof(f, runtime))
                    .collect(),
            ),
        ),
        (
            "then",
            JsonValue::Array(
                proof
                    .then
                    .iter()
                    .map(|f| project_fact_wd_proof(f, runtime))
                    .collect(),
            ),
        ),
            ])
}

fn project_forall_iff_wd(proof: &ForallFactWithIffWellDefinedProof, runtime: &Runtime) -> JsonValue {
    object_for(runtime, vec![
        ("type", string("forall_iff")),
        (
            "param_type_well_defined",
            JsonValue::Array(
                proof
                    .param_type_well_defined
                    .iter()
                    .map(|p| project_param_type_wd(p, runtime))
                    .collect(),
            ),
        ),
        (
            "dom",
            JsonValue::Array(
                proof
                    .dom
                    .iter()
                    .map(|f| project_fact_wd_proof(f, runtime))
                    .collect(),
            ),
        ),
        (
            "then",
            JsonValue::Array(
                proof
                    .then
                    .iter()
                    .map(|f| project_fact_wd_proof(f, runtime))
                    .collect(),
            ),
        ),
        (
            "iff",
            JsonValue::Array(
                proof
                    .iff
                    .iter()
                    .map(|f| project_fact_wd_proof(f, runtime))
                    .collect(),
            ),
        ),
            ])
}

fn project_not_forall_wd(proof: &NotForallFactWellDefinedProof, runtime: &Runtime) -> JsonValue {
    object_for(runtime, vec![
        ("type", string("not_forall")),
        (
            "param_type_well_defined",
            JsonValue::Array(
                proof
                    .param_type_well_defined
                    .iter()
                    .map(|p| project_param_type_wd(p, runtime))
                    .collect(),
            ),
        ),
        (
            "dom",
            JsonValue::Array(
                proof
                    .dom
                    .iter()
                    .map(|f| project_fact_wd_proof(f, runtime))
                    .collect(),
            ),
        ),
        (
            "then",
            JsonValue::Array(
                proof
                    .then
                    .iter()
                    .map(|f| project_fact_wd_proof(f, runtime))
                    .collect(),
            ),
        ),
            ])
}
