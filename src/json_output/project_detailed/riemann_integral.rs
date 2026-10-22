//! Integral WD exposes checked interval coverage and consumed selection evidence.
use super::verify::project_verify_fact;
use crate::execute::execute_fact_stmt::riemann_integral::*;
use crate::json_output::helper::{object_for, string};
use crate::knowledge_base::JsonValue;
use crate::runtime::Runtime;
pub(super) fn object_wd(p: &RiemannIntegralWellDefinedProof, rt: &Runtime) -> JsonValue {
    let selection = match &p.selection {
        RiemannIntegralSelectionProof::Candidate(c) => {
            super::searched::project_known_premise(c, rt)
        }
        RiemannIntegralSelectionProof::Existence { fact, proof } => object_for(
            rt,
            vec![
                ("existence", string(fact.readable_string())),
                ("proof", project_verify_fact(proof, rt)),
            ],
        ),
    };
    object_for(
        rt,
        vec![
            ("type", string("by_def")),
            ("family", string("IntegralOperator")),
            ("kind", string("Riemann")),
            (
                "function_wd",
                super::wd::project_obj_wd_proof(&p.function_wd, rt),
            ),
            ("lower_wd", super::wd::project_obj_wd_proof(&p.lower_wd, rt)),
            ("upper_wd", super::wd::project_obj_wd_proof(&p.upper_wd, rt)),
            (
                "function_domain",
                super::function_limit::domain(&p.domain, rt),
            ),
            (
                "requirements",
                JsonValue::Array(
                    p.requirements
                        .iter()
                        .map(|r| {
                            object_for(
                                rt,
                                vec![
                                    ("requirement", string(r.requirement.readable_string())),
                                    ("proof", project_verify_fact(&r.result, rt)),
                                ],
                            )
                        })
                        .collect(),
                ),
            ),
            ("selection", selection),
        ],
    )
}
pub(super) fn object_failure(p: &RiemannIntegralWellDefinedFailure, rt: &Runtime) -> JsonValue {
    let stage=match &p.stage {
        RiemannIntegralFailureStage::Domain=>object_for(rt,vec![("stage",string("domain")),("message",string("Requires a complete unary real function."))]),
        RiemannIntegralFailureStage::Requirement{requirement,result}=>object_for(rt,vec![("stage",string("interval_domain")),("requirement",string(requirement.readable_string())),("proof",project_verify_fact(result,rt))]),
        RiemannIntegralFailureStage::Selection(result)=>object_for(rt,vec![("stage",string("proved_integrability")),("message",string("Prove a finite Riemann integral candidate or integrability first; WD does not integrate the body.")),("requirement",project_verify_fact(result,rt))]),
    };
    object_for(
        rt,
        vec![
            ("type", string("obj_well_defined_failure")),
            ("kind", string("RiemannIntegral")),
            ("obj", string(p.obj.readable_string())),
            ("reason", stage),
        ],
    )
}
