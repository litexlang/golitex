//! Point derivative WD preserves the consumed candidate/existence evidence.
use super::verify::project_verify_fact;
use crate::execute::execute_fact_stmt::function_derivative::*;
use crate::json_output::helper::{object_for, string};
use crate::knowledge_base::JsonValue;
use crate::runtime::Runtime;
pub(super) fn object_wd(p: &DerivativeAtWellDefinedProof, rt: &Runtime) -> JsonValue {
    let convergence = match &p.convergence {
        DerivativeConvergenceProof::Candidate(c) => super::searched::project_known_premise(c, rt),
        DerivativeConvergenceProof::Existence { fact, proof } => object_for(
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
            ("family", string("DerivativeOperator")),
            ("kind", string("AtPoint")),
            (
                "function_wd",
                super::wd::project_obj_wd_proof(&p.function_wd, rt),
            ),
            ("point_wd", super::wd::project_obj_wd_proof(&p.point_wd, rt)),
            (
                "function_domain",
                super::function_limit::domain(&p.domain, rt),
            ),
            (
                "point_in_domain",
                project_verify_fact(&p.point_in_domain, rt),
            ),
            ("convergence", convergence),
        ],
    )
}
pub(super) fn object_failure(p: &DerivativeAtWellDefinedFailure, rt: &Runtime) -> JsonValue {
    let stage=match &p.stage {
        DerivativeWellDefinedFailureStage::Domain=>object_for(rt,vec![("stage",string("domain")),("message",string("Requires a complete unary real function."))]),
        DerivativeWellDefinedFailureStage::PointInDomain(result)=>object_for(rt,vec![("stage",string("point_in_domain")),("requirement",project_verify_fact(result,rt))]),
        DerivativeWellDefinedFailureStage::Convergence(result)=>object_for(rt,vec![
            ("stage",string("proved_derivative")),("message",string("Prove a finite derivative candidate or existence before selection; WD does not differentiate the body.")),
            ("requirement",project_verify_fact(result,rt))]),
    };
    object_for(
        rt,
        vec![
            ("type", string("obj_well_defined_failure")),
            ("kind", string("DerivativeAt")),
            ("obj", string(p.obj.readable_string())),
            ("reason", stage),
        ],
    )
}
