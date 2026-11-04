use crate::execute::execute_fact_stmt::verify_atomic_fact::search_native_matrix_property::{
    MatrixPropertyRequirementProof, MatrixPropertySumForm, NativeMatrixPropertyProof,
};
use crate::json_output::helper::{object_for, string};
use crate::knowledge_base::JsonValue;
use crate::prelude::*;

pub(super) fn project_matrix_property(
    proof: &NativeMatrixPropertyProof,
    runtime: &Runtime,
) -> JsonValue {
    let a = proof.application();
    let requirements = a
        .requirement_proofs
        .iter()
        .map(|proof| match proof {
            MatrixPropertyRequirementProof::Verified(proof) => {
                super::verify::project_verify_fact(proof, runtime)
            }
            MatrixPropertyRequirementProof::ZeroVectorAlpha {
                source,
                comparison,
                alpha,
            } => object_for(
                runtime,
                vec![
                    ("type", string("zero_vector_alpha")),
                    (
                        "source",
                        super::verify::project_verify_fact(source, runtime),
                    ),
                    (
                        "comparison",
                        string(AtomicFact::EqualFact(comparison.clone()).readable_string()),
                    ),
                    (
                        "alpha",
                        super::searched::project_they_are_the_same(alpha, runtime),
                    ),
                ],
            ),
        })
        .collect();
    let sum_form = match &a.sum_form {
        MatrixPropertySumForm::Original => string("original"),
        MatrixPropertySumForm::Natural { original, natural } => object_for(
            runtime,
            vec![
                ("type", string("unit_coefficients")),
                ("original", string(original.readable_string())),
                ("natural", string(natural.readable_string())),
            ],
        ),
    };
    object_for(
        runtime,
        vec![
            ("type", string("builtin_rule")),
            ("rule", string(proof.rule_name())),
            (
                "arguments",
                JsonValue::Array(
                    a.arguments
                        .iter()
                        .map(|o| string(o.readable_string()))
                        .collect(),
                ),
            ),
            ("schema", string(a.schema.readable_string())),
            ("sum_form", sum_form),
            ("conclusion", string(a.conclusion.readable_string())),
            ("reversed", JsonValue::Bool(a.matching.reversed)),
            (
                "comparisons",
                JsonValue::Array(
                    a.matching
                        .comparisons
                        .iter()
                        .map(|p| super::searched::project_equal_searched(p, runtime))
                        .collect(),
                ),
            ),
            (
                "requirements",
                JsonValue::Array(
                    a.requirements
                        .iter()
                        .map(|f| string(f.readable_string()))
                        .collect(),
                ),
            ),
            ("requirement_proofs", JsonValue::Array(requirements)),
        ],
    )
}
