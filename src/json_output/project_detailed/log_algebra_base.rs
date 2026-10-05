//! Exact selected legal-base guard, including the actual source direction.
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::log_algebra_base_proof::LogAlgebraBaseProof;
use crate::json_output::helper::{object_for, string};
use crate::knowledge_base::JsonValue;
use crate::runtime::Runtime;
use super::verify::project_verify_fact;

pub(super) fn project_log_algebra_base(proof: &LogAlgebraBaseProof, runtime: &Runtime) -> JsonValue {
    match proof {
        LogAlgebraBaseProof::GreaterThanOne(p) => object_for(runtime, vec![
            ("type", string("greater_than_one")),
            ("greater_than_one_proof", project_verify_fact(p, runtime)),
        ]),
        LogAlgebraBaseProof::BelowOne(p) => object_for(runtime, vec![
            ("type", string("below_one")),
            ("positive_proof", project_verify_fact(&p.positive_proof, runtime)),
            ("less_than_one_proof", project_verify_fact(&p.less_than_one_proof, runtime)),
        ]),
        LogAlgebraBaseProof::PositiveNonunit(p) => object_for(runtime, vec![
            ("type", string("positive_nonunit")),
            ("positive_proof", project_verify_fact(&p.positive_proof, runtime)),
            ("nonunit_proof", project_verify_fact(&p.nonunit_proof, runtime)),
        ]),
    }
}
