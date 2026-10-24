//! Matrix rules retain their real WD, domain, equality and scalar-carrier evidence.
use super::searched::project_known_equality_path;
use super::verify::project_verify_fact;
use super::wd::project_obj_wd_proof;
use crate::execute::execute_fact_stmt::native_matrix::*;
use crate::json_output::helper::{object_for, string};
use crate::knowledge_base::JsonValue;
use crate::runtime::Runtime;

fn real_operand(
    p: &crate::execute::execute_fact_stmt::matrix_operations::MatrixRealOperandProof,
    rt: &Runtime,
) -> JsonValue {
    use crate::execute::execute_fact_stmt::matrix_operations::MatrixRealOperandProof;
    match p {
        MatrixRealOperandProof::Membership(p) => project_verify_fact(p, rt),
        MatrixRealOperandProof::FiniteCoordinates(p) => object_for(
            rt,
            vec![
                ("kind", string("real_finite_coordinates")),
                (
                    "function_equal",
                    project_known_equality_path(&p.source.tuple_equal, rt),
                ),
                (
                    "coordinates",
                    JsonValue::Array(
                        p.coordinates
                            .iter()
                            .map(|p| project_verify_fact(p, rt))
                            .collect(),
                    ),
                ),
            ],
        ),
    }
}

pub(super) fn callable(p: &MatrixCallableProof, rt: &Runtime) -> JsonValue {
    let well_defined = match &p.well_defined {
        MatrixCallableWellDefinedProof::Checked(proof) => project_obj_wd_proof(proof, rt),
        MatrixCallableWellDefinedProof::ParentAtomic => {
            object_for(rt, vec![("kind", string("parent_atomic_well_defined"))])
        }
    };
    let carrier = match &p.scalar_carrier {
        MatrixFunctionScalarCarrierProof::RealOperands(proofs) => object_for(
            rt,
            vec![
                ("kind", string("real_operands")),
                (
                    "proofs",
                    crate::knowledge_base::JsonValue::Array(
                        proofs.iter().map(|p| real_operand(p, rt)).collect(),
                    ),
                ),
            ],
        ),
        MatrixFunctionScalarCarrierProof::RealConstants => {
            object_for(rt, vec![("kind", string("real_constants"))])
        }
        MatrixFunctionScalarCarrierProof::ComplexInput => {
            object_for(rt, vec![("kind", string("complex_input"))])
        }
        MatrixFunctionScalarCarrierProof::RealInput(proof) => object_for(
            rt,
            vec![
                ("kind", string("real_input")),
                ("proof", project_verify_fact(proof, rt)),
            ],
        ),
        MatrixFunctionScalarCarrierProof::RealReturnedFunction(proof) => object_for(
            rt,
            vec![
                ("kind", string("real_returned_function")),
                ("domain", super::function_domain::project_source(proof, rt)),
            ],
        ),
    };
    object_for(
        rt,
        vec![
            ("type", string("native_matrix_callable")),
            (
                "operator",
                string(crate::ast::obj::Obj::MatrixOperator(p.operator.clone()).readable_string()),
            ),
            (
                "function",
                string(
                    crate::ast::obj::Obj::FunctionSpace(
                        crate::ast::obj::FunctionSpace::AnonymousFn(p.function.clone()),
                    )
                    .readable_string(),
                ),
            ),
            (
                "function_equal",
                project_known_equality_path(&p.function_equal, rt),
            ),
            ("well_defined", well_defined),
            ("scalar_carrier", carrier),
        ],
    )
}
pub(super) fn membership(p: &MatrixMembershipProof, rt: &Runtime) -> JsonValue {
    let (kind, fields) = match p {
        MatrixMembershipProof::ExtendedScalar(p) => return extended_scalar(p, rt),
        MatrixMembershipProof::Space(p) => (
            "MatrixSpaceMember",
            vec![
                (
                    "signature",
                    string(
                        crate::ast::obj::Obj::FunctionSpace(crate::ast::obj::FunctionSpace::FnSet(
                            p.signature.clone(),
                        ))
                        .readable_string(),
                    ),
                ),
                (
                    "membership",
                    match &p.membership {
                        MatrixSpaceMembershipEvidence::Exact(proof) => object_for(
                            rt,
                            vec![
                                ("kind", string("exact_function_space")),
                                ("proof", project_verify_fact(proof, rt)),
                            ],
                        ),
                        MatrixSpaceMembershipEvidence::RealToComplex(proof) => object_for(
                            rt,
                            vec![
                                ("kind", string("real_to_complex_function_space")),
                                ("proof", project_verify_fact(proof, rt)),
                            ],
                        ),
                    },
                ),
            ],
        ),
        MatrixMembershipProof::Function(p) => (
            "MatrixFunctionMember",
            vec![
                ("callable", callable(&p.callable, rt)),
                (
                    "target",
                    string(
                        crate::ast::obj::Obj::FunctionSpace(crate::ast::obj::FunctionSpace::FnSet(
                            p.target.clone(),
                        ))
                        .readable_string(),
                    ),
                ),
            ],
        ),
        MatrixMembershipProof::Application(p) => (
            "MatrixApplicationInCodomain",
            vec![
                ("callable", callable(&p.callable, rt)),
                ("return_set", string(p.return_set.readable_string())),
            ],
        ),
        MatrixMembershipProof::ScalarComplex(_) => ("MatrixScalarComplex", vec![]),
        MatrixMembershipProof::ScalarReal(p) => (
            "MatrixScalarReal",
            vec![("input_is_real", project_verify_fact(&p.input_is_real, rt))],
        ),
    };
    let mut fields = fields;
    fields.insert(0, ("rule", string(kind)));
    object_for(rt, fields)
}

fn extended_scalar(
    p: &crate::execute::execute_fact_stmt::matrix_operations::ExtendedMatrixScalarMembershipProof,
    rt: &Runtime,
) -> JsonValue {
    use crate::execute::execute_fact_stmt::matrix_operations::*;
    fn carrier(p: &MatrixScalarCarrierProof, rt: &Runtime) -> JsonValue {
        match p {
            MatrixScalarCarrierProof::StandardSubset => string("standard_subset"),
            MatrixScalarCarrierProof::RealInputs(proofs) => {
                crate::knowledge_base::JsonValue::Array(
                    proofs.iter().map(|p| real_operand(p, rt)).collect(),
                )
            }
        }
    }
    let (kind, proof) = match p {
        ExtendedMatrixScalarMembershipProof::Rank(p) => {
            ("MatrixRankNatural", string(format!("{:?}", p.target)))
        }
        ExtendedMatrixScalarMembershipProof::Cofactor(p) => {
            ("MatrixCofactorCarrier", carrier(&p.carrier, rt))
        }
        ExtendedMatrixScalarMembershipProof::InnerProduct(p) => {
            ("FiniteInnerProductCarrier", carrier(&p.carrier, rt))
        }
        ExtendedMatrixScalarMembershipProof::EuclideanNorm(p) => {
            ("EuclideanNormReal", string(format!("{:?}", p.target)))
        }
        ExtendedMatrixScalarMembershipProof::FrobeniusNorm(p) => {
            ("MatrixFrobeniusNormReal", string(format!("{:?}", p.target)))
        }
    };
    object_for(rt, vec![("rule", string(kind)), ("carrier", proof)])
}
pub(super) fn equality(p: &MatrixEqualityProof, rt: &Runtime) -> JsonValue {
    let (kind, fields) = match p {
        MatrixEqualityProof::SpaceDefinition(p) => (
            "MatrixSpaceDefinition",
            vec![
                (
                    "signature",
                    string(
                        crate::ast::obj::Obj::FunctionSpace(crate::ast::obj::FunctionSpace::FnSet(
                            p.signature.clone(),
                        ))
                        .readable_string(),
                    ),
                ),
                ("equality", residual(&p.equality, rt)),
            ],
        ),
        MatrixEqualityProof::FunctionDefinition(p) => (
            "MatrixFunctionDefinition",
            vec![
                ("callable", callable(&p.callable, rt)),
                ("equality", residual(&p.equality, rt)),
            ],
        ),
        MatrixEqualityProof::ComponentDefinition(p) => (
            "MatrixComponentDefinition",
            vec![
                ("callable", callable(&p.callable, rt)),
                ("body", string(p.body.readable_string())),
                ("reduction", reduction(&p.reduction, rt)),
                ("equality", residual(&p.equality, rt)),
            ],
        ),
        MatrixEqualityProof::ScalarDefinition(p) => (
            "MatrixScalarDefinition",
            vec![
                ("expression", string(p.expression.readable_string())),
                ("equality", residual(&p.equality, rt)),
            ],
        ),
    };
    let mut fields = fields;
    fields.insert(0, ("rule", string(kind)));
    object_for(rt, fields)
}

fn reduction(p: &MatrixComponentReduction, rt: &Runtime) -> JsonValue {
    let evidence = match &p.evidence {
        MatrixComponentReductionEvidence::Unchanged => {
            object_for(rt, vec![("kind", string("unchanged"))])
        }
        MatrixComponentReductionEvidence::ConjugateArgument(arg) => object_for(
            rt,
            vec![
                ("kind", string("conjugate_argument")),
                ("argument", reduction(arg, rt)),
            ],
        ),
        MatrixComponentReductionEvidence::NativeApplication(step) => object_for(
            rt,
            vec![
                ("kind", string("native_matrix_application")),
                (
                    "application_well_defined",
                    project_obj_wd_proof(&step.application_well_defined, rt),
                ),
                ("callable", callable(&step.callable, rt)),
                ("body", string(step.body.readable_string())),
                ("continuation", reduction(&step.continuation, rt)),
            ],
        ),
    };
    object_for(
        rt,
        vec![
            ("value", string(p.value.readable_string())),
            ("evidence", evidence),
        ],
    )
}

fn residual(proof: &MatrixDefinitionResidualProof, rt: &Runtime) -> JsonValue {
    match proof {
        MatrixDefinitionResidualProof::Verified(p) => project_verify_fact(p, rt),
        MatrixDefinitionResidualProof::CheckedBeta(p) => object_for(
            rt,
            vec![
                ("kind", string("checked_residual_beta")),
                ("left", residual_beta(&p.left, rt)),
                ("right", residual_beta(&p.right, rt)),
                ("proof", project_verify_fact(&p.proof, rt)),
            ],
        ),
        MatrixDefinitionResidualProof::ExactEvaluation(p) => object_for(
            rt,
            vec![
                ("kind", string("exact_matrix_definition_evaluation")),
                ("left_value", string(p.left_value.readable_string())),
                ("right_value", string(p.right_value.readable_string())),
                (
                    "cited_equal_fact_ids",
                    JsonValue::Array(
                        p.cited_equal_fact_ids
                            .iter()
                            .map(|id| string(id.to_string()))
                            .collect(),
                    ),
                ),
                (
                    "matrix_scalar_evaluations",
                    super::aggregate_evaluation::project_matrix_scalar_evaluations(
                        &p.matrix_scalar_evaluations,
                        rt,
                    ),
                ),
                (
                    "aggregate_evaluations",
                    super::aggregate_evaluation::project_aggregate_evaluations(
                        &p.aggregate_evaluations,
                        rt,
                    ),
                ),
                (
                    "function_evaluations",
                    super::aggregate_evaluation::project_function_evaluations(
                        &p.function_evaluations,
                        rt,
                    ),
                ),
            ],
        ),
    }
}

fn residual_beta(p: &MatrixResidualBeta, rt: &Runtime) -> JsonValue {
    match p {
        MatrixResidualBeta::Unchanged(value) => object_for(
            rt,
            vec![
                ("kind", string("unchanged")),
                ("value", string(value.readable_string())),
            ],
        ),
        MatrixResidualBeta::Expanded(p) => object_for(
            rt,
            vec![
                ("kind", string("checked_function_body")),
                (
                    "application_well_defined",
                    project_obj_wd_proof(&p.application_well_defined, rt),
                ),
                (
                    "source",
                    super::function_body::project_parent_checked_function_body(&p.source, rt),
                ),
                ("body", string(p.body.readable_string())),
            ],
        ),
    }
}
