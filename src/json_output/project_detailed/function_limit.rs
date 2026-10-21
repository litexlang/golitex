//! Evidence for finite-point real function limits.
use crate::execute::execute_fact_stmt::function_limit::{
    FunctionConvergenceProof, FunctionLimitWDFailure, RealFunctionLimitDomainProof,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::FunctionLimitPredicateDomainProof;
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::{
    FailToVerifyFunctionLimitObjWellDefined, FunctionLimitObjWellDefinedProof,
};
use crate::json_output::helper::{object_for, string};
use crate::knowledge_base::JsonValue;
use crate::prelude::*;

pub(super) fn domain(p: &RealFunctionLimitDomainProof, rt: &Runtime) -> JsonValue {
    object_for(
        rt,
        vec![
            (
                "source",
                super::function_domain::project_source(&p.source, rt),
            ),
            ("domain", string(p.domain.readable_string())),
            (
                "input_real",
                super::verify::project_verify_fact(&p.input_real, rt),
            ),
            (
                "output_real",
                super::verify::project_verify_fact(&p.output_real, rt),
            ),
        ],
    )
}
pub(super) fn predicate_domain(p: &FunctionLimitPredicateDomainProof, rt: &Runtime) -> JsonValue {
    object_for(
        rt,
        vec![
            ("type", string("checked_real_function_limit_arguments")),
            ("function_domain", domain(&p.function_domain, rt)),
            ("point_real", approach_real(&p.approach_real, rt)),
            (
                "value_real",
                super::verify::project_verify_fact(&p.value_real, rt),
            ),
        ],
    )
}
pub(super) fn object_wd(p: &FunctionLimitObjWellDefinedProof, rt: &Runtime) -> JsonValue {
    let convergence = match &p.convergence {
        FunctionConvergenceProof::Candidate(c) => super::searched::project_known_premise(c, rt),
        FunctionConvergenceProof::Existence { proof, .. } => {
            super::verify::project_verify_fact(proof, rt)
        }
    };
    object_for(
        rt,
        vec![
            ("type", string("by_def")),
            ("family", string("LimitOperator")),
            ("kind", string("Function")),
            ("approach", string(p.approach.value_name())),
            (
                "function_wd",
                super::wd::project_obj_wd_proof(&p.function_wd, rt),
            ),
            ("approach_wd", approach_wd(&p.approach_wd, rt)),
            ("function_domain", domain(&p.function_domain, rt)),
            ("point_real", approach_real(&p.approach_real, rt)),
            ("convergence", convergence),
        ],
    )
}
pub(super) fn object_failure(
    p: &FailToVerifyFunctionLimitObjWellDefined,
    rt: &Runtime,
) -> JsonValue {
    let reason=match &p.reason {
        FunctionLimitWDFailure::Domain=>object_for(rt,vec![("message",string("Requires an unambiguous complete unary real domain, including guards."))]),
        FunctionLimitWDFailure::PointReal(result)=>object_for(rt,vec![
            ("type",string("point_real")),
            ("message",string("The finite approach point must be real.")),
            ("requirement",super::verify::project_verify_fact(result,rt)),
        ]),
        FunctionLimitWDFailure::Convergence(result)=>object_for(rt,vec![
            ("message",string("Function limit requires proved finite convergence; WD does not guess a limit.")),
            ("requirement",super::verify::project_verify_fact(result,rt)),
        ]),
    };
    object_for(
        rt,
        vec![
            ("kind", string("FunctionLimit")),
            ("obj", string(p.obj.readable_string())),
            ("reason", reason),
        ],
    )
}

fn approach_real(
    p:&crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::FunctionLimitApproachRealProof,
    rt: &Runtime,
) -> JsonValue {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::FunctionLimitApproachRealProof::*;
    match p {
        Finite(p) => super::verify::project_verify_fact(p, rt),
        AtPositiveInfinity => string("positive_infinity"),
        AtNegativeInfinity => string("negative_infinity"),
    }
}
fn approach_wd(
    p:&crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FunctionLimitApproachWellDefinedProof,
    rt: &Runtime,
) -> JsonValue {
    use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FunctionLimitApproachWellDefinedProof::*;
    match p {
        Finite { point_wd } => object_for(
            rt,
            vec![("point_wd", super::wd::project_obj_wd_proof(point_wd, rt))],
        ),
        AtPositiveInfinity => string("positive_infinity"),
        AtNegativeInfinity => string("negative_infinity"),
    }
}
