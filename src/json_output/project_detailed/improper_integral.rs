use crate::execute::execute_fact_stmt::improper_integral::*;
use crate::json_output::helper::{object_for, string};
use crate::knowledge_base::JsonValue;
use crate::runtime::Runtime;

pub(super) fn object_wd(proof: &ImproperIntegralWellDefinedProof, rt: &Runtime) -> JsonValue {
    object_for(
        rt,
        vec![
            ("type", string("by_def")),
            ("family", string("IntegralOperator")),
            ("kind", string("Improper")),
            (
                "children",
                JsonValue::Array(
                    proof
                        .children
                        .iter()
                        .map(|p| super::wd::project_obj_wd_proof(p, rt))
                        .collect(),
                ),
            ),
            (
                "integrability",
                super::verify::project_verify_fact(&proof.integrability, rt),
            ),
        ],
    )
}

pub(super) fn object_failure(
    proof: &ImproperIntegralWellDefinedFailure,
    rt: &Runtime,
) -> JsonValue {
    object_for(
        rt,
        vec![
            ("kind", string("ImproperIntegral")),
            ("obj", string(proof.obj.readable_string())),
            ("requirement", string(proof.requirement.readable_string())),
            (
                "result",
                super::verify::project_verify_fact(&proof.result, rt),
            ),
        ],
    )
}

pub(super) fn structural(proof: &ImproperIntegralStructuralProof, rt: &Runtime) -> JsonValue {
    object_for(
        rt,
        vec![
            ("type", string("builtin_strategy")),
            ("strategy", string("ImproperIntegral")),
            (
                "domain_requirements",
                JsonValue::Array(
                    proof
                        .domain_requirements
                        .iter()
                        .map(|p| super::verify::project_verify_fact(p, rt))
                        .collect(),
                ),
            ),
            (
                "domain_stores",
                JsonValue::Array(
                    proof
                        .domain_stores
                        .iter()
                        .map(|p| super::store::project_store_and_infer(p, rt))
                        .collect(),
                ),
            ),
            (
                "local_integrability",
                super::verify::project_verify_fact(&proof.local_integrability, rt),
            ),
            (
                "local_integrability_store",
                super::store::project_store_and_infer(&proof.local_integrability_store, rt),
            ),
            (
                "limits",
                JsonValue::Array(
                    proof
                        .limits
                        .iter()
                        .map(|limit| {
                            object_for(
                                rt,
                                vec![
                                    (
                                        "integrand_well_defined",
                                        super::wd::project_obj_wd_proof(&limit.integrand_wd, rt),
                                    ),
                                    (
                                        "introduced_parameter",
                                        super::verify::project_introduced_params(
                                            &limit.introduced_parameter,
                                            rt,
                                        ),
                                    ),
                                    (
                                        "integral",
                                        super::riemann_integral::structural(&limit.integral, rt),
                                    ),
                                    (
                                        "formula_well_defined",
                                        super::wd::project_obj_wd_proof(&limit.formula_wd, rt),
                                    ),
                                    ("limit", super::structural_limit::project(&limit.limit, rt)),
                                ],
                            )
                        })
                        .collect(),
                ),
            ),
            ("value", string(proof.value.readable_string())),
            (
                "comparison",
                super::verify::project_verify_fact(&proof.comparison, rt),
            ),
        ],
    )
}
