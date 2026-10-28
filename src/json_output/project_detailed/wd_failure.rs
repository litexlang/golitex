//! Exhaustive projection of existing WD failures; no new verifier behavior.
use super::verify::project_verify_fact;
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::fail_to_verify_obj_well_defined::*;
use crate::execute::execute_fact_stmt::FailToVerifyFactWellDefinedResult;
use crate::json_output::helper::{object_for, string};
use crate::knowledge_base::JsonValue;
use crate::runtime::Runtime;

fn node(rt: &Runtime, phase: &str, index: Option<usize>, failure: JsonValue) -> JsonValue {
    let mut entries = vec![("phase", string(phase)), ("failure", failure)];
    if let Some(index) = index {
        entries.push(("index", JsonValue::Number(index as f64)));
    }
    crate::json_output::helper::inherit_failure_field(rt, object_for(rt, entries), "failure")
}
fn message(rt: &Runtime, text: &str) -> JsonValue {
    crate::json_output::helper::with_failure_diagnostic(
        rt,
        object_for(rt, vec![("message", string(text))]),
        crate::json_output::failure_kind::FailureKind::WellDefined,
        vec![],
    )
}

pub(super) fn project_fact_wd_failure(
    f: &FailToVerifyFactWellDefinedResult,
    rt: &Runtime,
) -> JsonValue {
    use FailToVerifyFactWellDefinedResult::*;
    let projected = match f {
        Equality(p) => project_equal_wd_failure(p, rt),
        AtomicExceptEquality(p) => project_atomic_wd_failure(p, rt),
        AndFact(p) => node(rt, "component", Some(p.failed_index), project_atomic_wd_failure(&p.failed_component, rt)),
        ChainFact(p) => node(rt, "adjacent", Some(p.failed_index), project_atomic_wd_failure(&p.failed_adjacent, rt)),
        OrFact(p) => node(rt, "branch", Some(p.failed_index), project_fact_wd_failure(&p.failed_branch, rt)),
        ExistFact(p) => project_exist_wd_failure(p, rt),
        ForallFact(p) => project_forall_wd_failure(p, rt),
        ForallFactWithIff(p) => match p {
            crate::execute::execute_fact_stmt::verify_forall_fact_with_iff::FailToVerifyForallFactWithIffWellDefinedResult::ParamType { reason: p, .. } => node(rt, "parameter_type", None, project_obj_wd_failure(p, rt)),
            crate::execute::execute_fact_stmt::verify_forall_fact_with_iff::FailToVerifyForallFactWithIffWellDefinedResult::DomFact { failed_index, failed_dom, .. } => node(rt, "failed_dom", Some(*failed_index), project_fact_wd_failure(failed_dom, rt)),
            crate::execute::execute_fact_stmt::verify_forall_fact_with_iff::FailToVerifyForallFactWithIffWellDefinedResult::ThenFact { failed_index, failed_then, .. } => node(rt, "failed_then", Some(*failed_index), project_fact_wd_failure(failed_then, rt)),
            crate::execute::execute_fact_stmt::verify_forall_fact_with_iff::FailToVerifyForallFactWithIffWellDefinedResult::IffFact { failed_index, failed_iff, .. } => node(rt, "failed_iff", Some(*failed_index), project_fact_wd_failure(failed_iff, rt)),
        },
        NotForall(p) => match p {
            crate::execute::execute_fact_stmt::verify_not_forall_fact::FailToVerifyNotForallFactWellDefinedResult::ParamType { reason: p, .. } => node(rt, "parameter_type", None, project_obj_wd_failure(p, rt)),
            crate::execute::execute_fact_stmt::verify_not_forall_fact::FailToVerifyNotForallFactWellDefinedResult::DomFact { failed_index, failed_dom, .. } => node(rt, "failed_dom", Some(*failed_index), project_fact_wd_failure(failed_dom, rt)),
            crate::execute::execute_fact_stmt::verify_not_forall_fact::FailToVerifyNotForallFactWellDefinedResult::ThenFact { failed_index, failed_then, .. } => node(rt, "failed_then", Some(*failed_index), project_fact_wd_failure(failed_then, rt)),
        },
    };
    with_fact(rt, projected, f.fact())
}

pub(super) fn project_exist_wd_failure(
    failure: &crate::execute::execute_fact_stmt::verify_exist_shaped_fact::FailToVerifyExistShapedFactWellDefinedResult,
    rt: &Runtime,
) -> JsonValue {
    use crate::execute::execute_fact_stmt::verify_exist_shaped_fact::FailToVerifyExistShapedFactWellDefinedResult;
    let projected = match failure {
        FailToVerifyExistShapedFactWellDefinedResult::ParamType { reason: failed, .. } => node(
            rt,
            "parameter_type",
            None,
            project_obj_wd_failure(failed, rt),
        ),
        FailToVerifyExistShapedFactWellDefinedResult::BodyFact {
            failed_index,
            failed_body,
            ..
        } => node(
            rt,
            "failed_body",
            Some(*failed_index),
            project_fact_wd_failure(failed_body, rt),
        ),
    };
    with_fact(
        rt,
        projected,
        crate::ast::fact::exist_shaped_fact_to_fact(failure.fact()),
    )
}

pub(super) fn project_forall_wd_failure(
    failure: &crate::execute::execute_fact_stmt::verify_forall_fact::FailToVerifyForallFactWellDefinedResult,
    rt: &Runtime,
) -> JsonValue {
    use crate::execute::execute_fact_stmt::verify_forall_fact::FailToVerifyForallFactWellDefinedResult::*;
    let projected = match failure {
        ParamType { reason: p, .. } => {
            node(rt, "parameter_type", None, project_obj_wd_failure(p, rt))
        }
        AutoOpenStructLayer { reason: failed, .. } => {
            crate::json_output::helper::with_failure_diagnostic(
                rt,
                super::definition_failure::project_struct_layer_failure(failed, rt),
                crate::json_output::failure_kind::FailureKind::WellDefined,
                vec![],
            )
        }
        DomFact {
            failed_index,
            failed_dom,
            ..
        } => node(
            rt,
            "failed_dom",
            Some(*failed_index),
            project_fact_wd_failure(failed_dom, rt),
        ),
        ThenFact {
            failed_index,
            failed_then,
            ..
        } => node(
            rt,
            "failed_then",
            Some(*failed_index),
            project_fact_wd_failure(failed_then, rt),
        ),
    };
    with_fact(
        rt,
        projected,
        crate::ast::fact::Fact::ForallFact(failure.fact().clone()),
    )
}

pub(super) fn project_equal_wd_failure(
    failure: &crate::execute::execute_fact_stmt::FailToVerifyEqualFactWellDefinedResult,
    rt: &Runtime,
) -> JsonValue {
    let mut output = project_obj_wd_failure(&failure.reason, rt);
    if let JsonValue::Object(fields) = &mut output {
        fields.insert(
            crate::json_output::json_keys::localize_key(
                "fact",
                rt.launch_command.output_language(),
            ),
            string(crate::ast::fact::AtomicFact::EqualFact(failure.fact.clone()).readable_string()),
        );
        fields.insert(
            crate::json_output::json_keys::localize_key(
                "failed_obj",
                rt.launch_command.output_language(),
            ),
            string(failure.failed_obj.readable_string()),
        );
    }
    output
}

pub(super) fn project_atomic_wd_failure(
    failure: &crate::execute::execute_fact_stmt::verify_atomic_fact::FailToVerifyAtomicFactWellDefinedResult,
    rt: &Runtime,
) -> JsonValue {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::{
        FailToVerifyAtomicFactWellDefinedResult, PredicateSignatureWellDefinedFailure,
    };
    let mut projected = match failure {
        FailToVerifyAtomicFactWellDefinedResult::RealAnalysisDomain { fact, well_defined_of_each_parameter } => object_for(rt, vec![
            ("phase", string("real_analysis_domain")),
            ("fact", string(fact.readable_string())),
            ("well_defined_of_each_parameter", JsonValue::Array(well_defined_of_each_parameter.iter().map(|p| super::wd::project_obj_wd_proof(p, rt)).collect())),
            ("message", string("Requires a complete real sequence or an unambiguous complete unary real function domain, including guards.")),
        ]),
        FailToVerifyAtomicFactWellDefinedResult::FunctionLimitDomain { function, .. } => {
            object_for(
                rt,
                vec![
                    ("phase", string("function_limit_domain")),
                    ("function", string(function.readable_string())),
                    (
                        "message",
                        string(
                            "Requires an unambiguous complete unary real domain, including guards.",
                        ),
                    ),
                ],
            )
        }
        FailToVerifyAtomicFactWellDefinedResult::Argument { reason, .. } => {
            project_obj_wd_failure(reason, rt)
        }
        FailToVerifyAtomicFactWellDefinedResult::Domain {
            requirement,
            result,
            completed,
            ..
        } => object_for(
            rt,
            vec![
                ("phase", string("predicate_domain")),
                (
                    "completed_requirements",
                    JsonValue::Array(
                        completed
                            .iter()
                            .map(|p| {
                                object_for(
                                    rt,
                                    vec![
                                        ("requirement", string(p.requirement.readable_string())),
                                        ("verify", project_verify_fact(&p.result, rt)),
                                    ],
                                )
                            })
                            .collect(),
                    ),
                ),
                ("requirement", string(requirement.readable_string())),
                ("verify", project_verify_fact(result, rt)),
            ],
        ),
        FailToVerifyAtomicFactWellDefinedResult::Predicate {
            well_defined_of_each_parameter,
            reason,
            ..
        } => {
            let mut fields = vec![
                ("phase", string("predicate_signature")),
                (
                    "well_defined_of_each_parameter",
                    JsonValue::Array(
                        well_defined_of_each_parameter
                            .iter()
                            .map(|p| super::wd::project_obj_wd_proof(p, rt))
                            .collect(),
                    ),
                ),
            ];
            match reason {
                PredicateSignatureWellDefinedFailure::Undefined { predicate } => fields.extend([
                    ("reason", string("undefined_predicate")),
                    ("predicate", string(predicate.display_string())),
                ]),
                PredicateSignatureWellDefinedFailure::Retired { predicate } => fields.extend([
                    ("reason", string("retired_builtin")),
                    ("predicate", string(predicate.display_string())),
                ]),
                PredicateSignatureWellDefinedFailure::Arity {
                    predicate,
                    expected,
                    actual,
                } => fields.extend([
                    ("reason", string("arity")),
                    ("predicate", string(predicate.display_string())),
                    ("expected", JsonValue::Number(*expected as f64)),
                    ("actual", JsonValue::Number(*actual as f64)),
                ]),
            }
            object_for(rt, fields)
        }
    };
    if let JsonValue::Object(fields) = &mut projected {
        fields.insert(
            crate::json_output::json_keys::localize_key(
                "fact",
                rt.launch_command.output_language(),
            ),
            string(failure.fact().readable_string()),
        );
    }
    let mut details = Vec::new();
    if let FailToVerifyAtomicFactWellDefinedResult::Domain { requirement, .. } = failure {
        details.push(("obligation", string(requirement.readable_string())));
    }
    crate::json_output::helper::with_failure_diagnostic(
        rt,
        projected,
        crate::json_output::failure_kind::FailureKind::WellDefined,
        details,
    )
}

fn common(f: &FailToVerifyObjWellDefinedByDefCommon, rt: &Runtime) -> JsonValue {
    let projected = match f {
        FailToVerifyObjWellDefinedByDefCommon::Child { obj, child } => object_for(
            rt,
            vec![
                ("phase", string("child")),
                ("obj", string(obj.readable_string())),
                ("failure", project_obj_wd_failure(child, rt)),
            ],
        ),
        FailToVerifyObjWellDefinedByDefCommon::Requirement { obj, result } => {
            let projected = object_for(
                rt,
                vec![
                    ("phase", string("requirement")),
                    ("obj", string(obj.readable_string())),
                    ("result", project_verify_fact(result, rt)),
                ],
            );
            let projected =
                crate::json_output::helper::inherit_failure_field(rt, projected, "result");
            let mut details = vec![("expression", string(obj.readable_string()))];
            if !result.is_wd_failed() {
                details.push((
                    "obligation",
                    string(crate::json_output::project_normal::verify_goal_display(
                        result,
                    )),
                ));
            }
            return crate::json_output::helper::with_failure_diagnostic(
                rt,
                projected,
                crate::json_output::failure_kind::FailureKind::WellDefined,
                details,
            );
        }
        FailToVerifyObjWellDefinedByDefCommon::Others(text) => message(rt, text),
    };
    crate::json_output::helper::inherit_failure_field(rt, projected, "failure")
}

pub(super) fn project_obj_wd_failure(
    f: &FailToVerifyObjWellDefinedResult,
    rt: &Runtime,
) -> JsonValue {
    let projected = match f {
        FailToVerifyObjWellDefinedResult::LimitOperator(FailToVerifyLimitOperatorObjWellDefinedResult::MultivariableScalar(p)) => super::multivariable::object_failure(&p.stage,rt),
        FailToVerifyObjWellDefinedResult::LimitOperator(FailToVerifyLimitOperatorObjWellDefinedResult::MultivariableVector(p)) => super::multivariable::object_failure(&p.stage,rt),
        FailToVerifyObjWellDefinedResult::DerivativeOperator(crate::execute::execute_fact_stmt::function_derivative::DerivativeOperatorWellDefinedFailure::Partial(p)) => super::multivariable::object_failure(&p.stage,rt),
        FailToVerifyObjWellDefinedResult::DerivativeOperator(crate::execute::execute_fact_stmt::function_derivative::DerivativeOperatorWellDefinedFailure::ScalarDifferential(p)) => super::multivariable::object_failure(&p.stage,rt),
        FailToVerifyObjWellDefinedResult::DerivativeOperator(crate::execute::execute_fact_stmt::function_derivative::DerivativeOperatorWellDefinedFailure::TotalDifferential(p)) => super::multivariable::object_failure(&p.stage,rt),
        FailToVerifyObjWellDefinedResult::DerivativeOperator(crate::execute::execute_fact_stmt::function_derivative::DerivativeOperatorWellDefinedFailure::Gradient(p)) => super::multivariable::object_failure(&p.stage,rt),
        FailToVerifyObjWellDefinedResult::DerivativeOperator(crate::execute::execute_fact_stmt::function_derivative::DerivativeOperatorWellDefinedFailure::Jacobian(p)) => super::multivariable::object_failure(&p.stage,rt),
        FailToVerifyObjWellDefinedResult::DerivativeOperator(crate::execute::execute_fact_stmt::function_derivative::DerivativeOperatorWellDefinedFailure::Hessian(p)) => super::multivariable::object_failure(&p.stage,rt),
        FailToVerifyObjWellDefinedResult::DerivativeOperator(crate::execute::execute_fact_stmt::function_derivative::DerivativeOperatorWellDefinedFailure::Divergence(p)) => super::multivariable::object_failure(&p.stage,rt),
        FailToVerifyObjWellDefinedResult::DerivativeOperator(crate::execute::execute_fact_stmt::function_derivative::DerivativeOperatorWellDefinedFailure::Curl(p)) => super::multivariable::object_failure(&p.stage,rt),
        FailToVerifyObjWellDefinedResult::DerivativeOperator(crate::execute::execute_fact_stmt::function_derivative::DerivativeOperatorWellDefinedFailure::Laplacian(p)) => super::multivariable::object_failure(&p.stage,rt),
        FailToVerifyObjWellDefinedResult::MatrixOperator(value) => match value {
            FailToVerifyMatrixOperatorObjWellDefinedResult::Determinant(p) => node(rt, "Determinant", None, common(&p.0, rt)),
            FailToVerifyMatrixOperatorObjWellDefinedResult::ZeroMatrix(p) => node(rt, "ZeroMatrix", None, common(&p.0, rt)),
            FailToVerifyMatrixOperatorObjWellDefinedResult::IdentityMatrix(p) => node(rt, "IdentityMatrix", None, common(&p.0, rt)),
            FailToVerifyMatrixOperatorObjWellDefinedResult::Transpose(p) => node(rt, "Transpose", None, common(&p.0, rt)),
            FailToVerifyMatrixOperatorObjWellDefinedResult::ConjugateTranspose(p) => node(rt, "ConjugateTranspose", None, common(&p.0, rt)),
            FailToVerifyMatrixOperatorObjWellDefinedResult::Add(p) => node(rt,"Add",None,common(&p.0,rt)),
            FailToVerifyMatrixOperatorObjWellDefinedResult::Subtract(p) => node(rt,"Subtract",None,common(&p.0,rt)),
            FailToVerifyMatrixOperatorObjWellDefinedResult::Scale(p) => node(rt,"Scale",None,common(&p.0,rt)),
            FailToVerifyMatrixOperatorObjWellDefinedResult::Multiply(p) => node(rt,"Multiply",None,common(&p.0,rt)),
            FailToVerifyMatrixOperatorObjWellDefinedResult::Apply(p) => node(rt,"Apply",None,common(&p.0,rt)),
            FailToVerifyMatrixOperatorObjWellDefinedResult::Power(p) => node(rt,"Power",None,common(&p.0,rt)),
            FailToVerifyMatrixOperatorObjWellDefinedResult::Inverse(p) => node(rt,"Inverse",None,common(&p.0,rt)),
            FailToVerifyMatrixOperatorObjWellDefinedResult::Rank(p) => node(rt,"Rank",None,common(&p.0,rt)),
            FailToVerifyMatrixOperatorObjWellDefinedResult::Minor(p) => node(rt,"Minor",None,common(&p.0,rt)),
            FailToVerifyMatrixOperatorObjWellDefinedResult::Cofactor(p) => node(rt,"Cofactor",None,common(&p.0,rt)),
            FailToVerifyMatrixOperatorObjWellDefinedResult::Adjugate(p) => node(rt,"Adjugate",None,common(&p.0,rt)),
            FailToVerifyMatrixOperatorObjWellDefinedResult::Diagonal(p) => node(rt,"Diagonal",None,common(&p.0,rt)),
            FailToVerifyMatrixOperatorObjWellDefinedResult::OuterProduct(p) => node(rt,"OuterProduct",None,common(&p.0,rt)),
            FailToVerifyMatrixOperatorObjWellDefinedResult::InnerProduct(p) => node(rt,"InnerProduct",None,common(&p.0,rt)),
            FailToVerifyMatrixOperatorObjWellDefinedResult::EuclideanNorm(p) => node(rt,"EuclideanNorm",None,common(&p.0,rt)),
            FailToVerifyMatrixOperatorObjWellDefinedResult::FrobeniusNorm(p) => node(rt,"FrobeniusNorm",None,common(&p.0,rt)),
            FailToVerifyMatrixOperatorObjWellDefinedResult::Trace(p) => node(rt, "Trace", None, common(&p.0, rt)),
        },

        FailToVerifyObjWellDefinedResult::IntegralOperator(crate::execute::execute_fact_stmt::riemann_integral::IntegralOperatorWellDefinedFailure::Riemann(p))=>super::riemann_integral::object_failure(p,rt),
        FailToVerifyObjWellDefinedResult::DerivativeOperator(crate::execute::execute_fact_stmt::function_derivative::DerivativeOperatorWellDefinedFailure::AtPoint(p)) => super::function_derivative::object_failure(p,rt),
        FailToVerifyObjWellDefinedResult::BoundOperator(FailToVerifyBoundOperatorObjWellDefinedResult::Supremum(p)) => node(rt,"Supremum",None,
            object_for(rt,vec![("obj",string(p.obj.readable_string())),("requirement",project_verify_fact(&p.result,rt))])),
        FailToVerifyObjWellDefinedResult::BoundOperator(FailToVerifyBoundOperatorObjWellDefinedResult::Infimum(p)) => node(rt,"Infimum",None,
            object_for(rt,vec![("obj",string(p.obj.readable_string())),("requirement",project_verify_fact(&p.result,rt))])),
        FailToVerifyObjWellDefinedResult::LimitOperator(FailToVerifyLimitOperatorObjWellDefinedResult::Function(p)) => super::function_limit::object_failure(p,rt),
        FailToVerifyObjWellDefinedResult::LimitOperator(FailToVerifyLimitOperatorObjWellDefinedResult::Sequence(p)) => node(rt,"SequenceLimit",None,
            object_for(rt,vec![("obj",string(p.obj.readable_string())),("message",string("Sequence limit requires proved finite convergence; no limit is guessed from the body.")),("requirement",project_verify_fact(&p.result,rt))])),
        FailToVerifyObjWellDefinedResult::LimitOperator(FailToVerifyLimitOperatorObjWellDefinedResult::SequenceLimsup(p)) => node(rt,"SequenceLimsup",None,
            object_for(rt,vec![("obj",string(p.obj.readable_string())),("message",string("limsup requires a proved finite candidate or existence; WD does not guess from the body.")),("requirement",project_verify_fact(&p.result,rt))])),
        FailToVerifyObjWellDefinedResult::LimitOperator(FailToVerifyLimitOperatorObjWellDefinedResult::SequenceLiminf(p)) => node(rt,"SequenceLiminf",None,
            object_for(rt,vec![("obj",string(p.obj.readable_string())),("message",string("liminf requires a proved finite candidate or existence; WD does not guess from the body.")),("requirement",project_verify_fact(&p.result,rt))])),


        FailToVerifyObjWellDefinedResult::Identifier(p) => node(
            rt,
            "Identifier",
            None,
            project_leaf_fail_to_verify_identifier_obj_well_defined(p, rt),
        ),
        FailToVerifyObjWellDefinedResult::FnObj(p) => node(
            rt,
            "FnObj",
            None,
            project_leaf_fail_to_verify_fn_obj_obj_well_defined(p, rt),
        ),
        FailToVerifyObjWellDefinedResult::Literal(p) => node(
            rt,
            "Literal",
            None,
            project_fail_to_verify_literal_obj_well_defined_result(p, rt),
        ),
        FailToVerifyObjWellDefinedResult::StandardSet(p) => node(
            rt,
            "StandardSet",
            None,
            project_leaf_fail_to_verify_standard_set_obj_well_defined(p, rt),
        ),
        FailToVerifyObjWellDefinedResult::ArithmeticOperator(p) => node(
            rt,
            "ArithmeticOperator",
            None,
            project_fail_to_verify_arithmetic_operator_obj_well_defined_result(p, rt),
        ),
        FailToVerifyObjWellDefinedResult::IntegerOperator(p) => node(
            rt,
            "IntegerOperator",
            None,
            project_fail_to_verify_integer_operator_obj_well_defined_result(p, rt),
        ),
        FailToVerifyObjWellDefinedResult::HyperbolicOperator(p) => node(
            rt,
            "HyperbolicOperator",
            None,
            match p {
                FailToVerifyHyperbolicOperatorObjWellDefinedResult::Sinh(p) => {
                    node(rt, "Sinh", None, common(&p.0, rt))
                }
                FailToVerifyHyperbolicOperatorObjWellDefinedResult::Cosh(p) => {
                    node(rt, "Cosh", None, common(&p.0, rt))
                }
                FailToVerifyHyperbolicOperatorObjWellDefinedResult::Tanh(p) => {
                    node(rt, "Tanh", None, common(&p.0, rt))
                }
                FailToVerifyHyperbolicOperatorObjWellDefinedResult::Coth(p) => {
                    node(rt, "Coth", None, common(&p.0, rt))
                }
                FailToVerifyHyperbolicOperatorObjWellDefinedResult::Sech(p) => {
                    node(rt, "Sech", None, common(&p.0, rt))
                }
                FailToVerifyHyperbolicOperatorObjWellDefinedResult::Csch(p) => {
                    node(rt, "Csch", None, common(&p.0, rt))
                }
            },
        ),
        FailToVerifyObjWellDefinedResult::TrigOperator(p) => node(
            rt,
            "TrigOperator",
            None,
            project_fail_to_verify_trig_operator_obj_well_defined_result(p, rt),
        ),
        FailToVerifyObjWellDefinedResult::ExpLogOperator(p) => node(
            rt,
            "ExpLogOperator",
            None,
            project_fail_to_verify_exp_log_operator_obj_well_defined_result(p, rt),
        ),
        FailToVerifyObjWellDefinedResult::ComplexOperator(p) => node(
            rt,
            "ComplexOperator",
            None,
            project_fail_to_verify_complex_operator_obj_well_defined_result(p, rt),
        ),
        FailToVerifyObjWellDefinedResult::SetOperator(p) => node(
            rt,
            "SetOperator",
            None,
            project_fail_to_verify_set_operator_obj_well_defined_result(p, rt),
        ),
        FailToVerifyObjWellDefinedResult::SetFormer(p) => node(
            rt,
            "SetFormer",
            None,
            project_fail_to_verify_set_former_obj_well_defined_result(p, rt),
        ),
        FailToVerifyObjWellDefinedResult::ProductShape(p) => node(
            rt,
            "ProductShape",
            None,
            project_fail_to_verify_product_shape_obj_well_defined_result(p, rt),
        ),
        FailToVerifyObjWellDefinedResult::FunctionSpace(p) => node(
            rt,
            "FunctionSpace",
            None,
            project_fail_to_verify_function_space_obj_well_defined_result(p, rt),
        ),
        FailToVerifyObjWellDefinedResult::IteratedOperator(p) => node(
            rt,
            "IteratedOperator",
            None,
            project_fail_to_verify_iterated_operator_obj_well_defined_result(p, rt),
        ),
        FailToVerifyObjWellDefinedResult::FiniteSetStat(p) => node(
            rt,
            "FiniteSetStat",
            None,
            project_fail_to_verify_finite_set_stat_obj_well_defined_result(p, rt),
        ),
        FailToVerifyObjWellDefinedResult::Structish(p) => node(
            rt,
            "Structish",
            None,
            project_fail_to_verify_structish_obj_well_defined_result(p, rt),
        ),
        FailToVerifyObjWellDefinedResult::InstantiatedTemplateObj(p) => {
            node(rt, "InstantiatedTemplateObj", None, common(&p.0, rt))
        }
    };
    crate::json_output::helper::with_failure_diagnostic(
        rt,
        projected,
        crate::json_output::failure_kind::FailureKind::WellDefined,
        vec![],
    )
}

fn project_fail_to_verify_literal_obj_well_defined_result(
    f: &FailToVerifyLiteralObjWellDefinedResult,
    rt: &Runtime,
) -> JsonValue {
    match f {
        FailToVerifyLiteralObjWellDefinedResult::Number(p) => node(
            rt,
            "Number",
            None,
            project_leaf_fail_to_verify_number_obj_well_defined(p, rt),
        ),
        FailToVerifyLiteralObjWellDefinedResult::ImaginaryUnit(p) => node(
            rt,
            "ImaginaryUnit",
            None,
            project_leaf_fail_to_verify_imaginary_unit_obj_well_defined(p, rt),
        ),
        FailToVerifyLiteralObjWellDefinedResult::EulerNumber(p) => node(
            rt,
            "EulerNumber",
            None,
            project_leaf_fail_to_verify_euler_number_obj_well_defined(p, rt),
        ),
        FailToVerifyLiteralObjWellDefinedResult::Pi(p) => node(
            rt,
            "Pi",
            None,
            project_leaf_fail_to_verify_pi_obj_well_defined(p, rt),
        ),
    }
}

fn project_fail_to_verify_arithmetic_operator_obj_well_defined_result(
    f: &FailToVerifyArithmeticOperatorObjWellDefinedResult,
    rt: &Runtime,
) -> JsonValue {
    match f {
        FailToVerifyArithmeticOperatorObjWellDefinedResult::Add(p) => {
            node(rt, "Add", None, common(&p.0, rt))
        }
        FailToVerifyArithmeticOperatorObjWellDefinedResult::Sub(p) => {
            node(rt, "Sub", None, common(&p.0, rt))
        }
        FailToVerifyArithmeticOperatorObjWellDefinedResult::Neg(p) => {
            node(rt, "Neg", None, common(&p.0, rt))
        }
        FailToVerifyArithmeticOperatorObjWellDefinedResult::Mul(p) => {
            node(rt, "Mul", None, common(&p.0, rt))
        }
        FailToVerifyArithmeticOperatorObjWellDefinedResult::Div(p) => {
            node(rt, "Div", None, common(&p.0, rt))
        }
        FailToVerifyArithmeticOperatorObjWellDefinedResult::Pow(p) => {
            node(rt, "Pow", None, common(&p.0, rt))
        }
        FailToVerifyArithmeticOperatorObjWellDefinedResult::Abs(p) => {
            node(rt, "Abs", None, common(&p.0, rt))
        }
        FailToVerifyArithmeticOperatorObjWellDefinedResult::Min(p) => {
            node(rt, "Min", None, common(&p.0, rt))
        }
        FailToVerifyArithmeticOperatorObjWellDefinedResult::Max(p) => {
            node(rt, "Max", None, common(&p.0, rt))
        }
        FailToVerifyArithmeticOperatorObjWellDefinedResult::Floor(p) => {
            node(rt, "Floor", None, common(&p.0, rt))
        }
        FailToVerifyArithmeticOperatorObjWellDefinedResult::Ceil(p) => {
            node(rt, "Ceil", None, common(&p.0, rt))
        }
        FailToVerifyArithmeticOperatorObjWellDefinedResult::Sign(p) => {
            node(rt, "Sign", None, common(&p.0, rt))
        }
    }
}

fn project_fail_to_verify_integer_operator_obj_well_defined_result(
    f: &FailToVerifyIntegerOperatorObjWellDefinedResult,
    rt: &Runtime,
) -> JsonValue {
    match f {
        FailToVerifyIntegerOperatorObjWellDefinedResult::Mod(p) => {
            node(rt, "Mod", None, common(&p.0, rt))
        }
        FailToVerifyIntegerOperatorObjWellDefinedResult::Quot(p) => {
            node(rt, "Quot", None, common(&p.0, rt))
        }
        FailToVerifyIntegerOperatorObjWellDefinedResult::Gcd(p) => {
            node(rt, "Gcd", None, common(&p.0, rt))
        }
        FailToVerifyIntegerOperatorObjWellDefinedResult::Lcm(p) => {
            node(rt, "Lcm", None, common(&p.0, rt))
        }
        FailToVerifyIntegerOperatorObjWellDefinedResult::Factorial(p) => {
            node(rt, "Factorial", None, common(&p.0, rt))
        }
    }
}

fn project_fail_to_verify_trig_operator_obj_well_defined_result(
    f: &FailToVerifyTrigOperatorObjWellDefinedResult,
    rt: &Runtime,
) -> JsonValue {
    match f {
        FailToVerifyTrigOperatorObjWellDefinedResult::Csc(p) => {
            node(rt, "Csc", None, common(&p.0, rt))
        }
        FailToVerifyTrigOperatorObjWellDefinedResult::Sec(p) => {
            node(rt, "Sec", None, common(&p.0, rt))
        }
        FailToVerifyTrigOperatorObjWellDefinedResult::Sin(p) => {
            node(rt, "Sin", None, common(&p.0, rt))
        }
        FailToVerifyTrigOperatorObjWellDefinedResult::Cos(p) => {
            node(rt, "Cos", None, common(&p.0, rt))
        }
        FailToVerifyTrigOperatorObjWellDefinedResult::Tan(p) => {
            node(rt, "Tan", None, common(&p.0, rt))
        }
        FailToVerifyTrigOperatorObjWellDefinedResult::Cot(p) => {
            node(rt, "Cot", None, common(&p.0, rt))
        }
        FailToVerifyTrigOperatorObjWellDefinedResult::Arcsin(p) => {
            node(rt, "Arcsin", None, common(&p.0, rt))
        }
        FailToVerifyTrigOperatorObjWellDefinedResult::Arccos(p) => {
            node(rt, "Arccos", None, common(&p.0, rt))
        }
        FailToVerifyTrigOperatorObjWellDefinedResult::Arctan(p) => {
            node(rt, "Arctan", None, common(&p.0, rt))
        }
        FailToVerifyTrigOperatorObjWellDefinedResult::Arccot(p) => {
            node(rt, "Arccot", None, common(&p.0, rt))
        }
    }
}

fn project_fail_to_verify_exp_log_operator_obj_well_defined_result(
    f: &FailToVerifyExpLogOperatorObjWellDefinedResult,
    rt: &Runtime,
) -> JsonValue {
    match f {
        FailToVerifyExpLogOperatorObjWellDefinedResult::Exp(p) => {
            node(rt, "Exp", None, common(&p.0, rt))
        }
        FailToVerifyExpLogOperatorObjWellDefinedResult::Ln(p) => {
            node(rt, "Ln", None, common(&p.0, rt))
        }
        FailToVerifyExpLogOperatorObjWellDefinedResult::Log(p) => {
            node(rt, "Log", None, common(&p.0, rt))
        }
        FailToVerifyExpLogOperatorObjWellDefinedResult::Sqrt(p) => {
            node(rt, "Sqrt", None, common(&p.0, rt))
        }
    }
}

fn project_fail_to_verify_complex_operator_obj_well_defined_result(
    f: &FailToVerifyComplexOperatorObjWellDefinedResult,
    rt: &Runtime,
) -> JsonValue {
    match f {
        FailToVerifyComplexOperatorObjWellDefinedResult::Conjugate(p) => {
            node(rt, "Conjugate", None, common(&p.0, rt))
        }
        FailToVerifyComplexOperatorObjWellDefinedResult::RealPart(p) => {
            node(rt, "RealPart", None, common(&p.0, rt))
        }
        FailToVerifyComplexOperatorObjWellDefinedResult::ImaginaryPart(p) => {
            node(rt, "ImaginaryPart", None, common(&p.0, rt))
        }
        FailToVerifyComplexOperatorObjWellDefinedResult::ComplexAbs(p) => {
            node(rt, "ComplexAbs", None, common(&p.0, rt))
        }
    }
}

fn project_fail_to_verify_set_operator_obj_well_defined_result(
    f: &FailToVerifySetOperatorObjWellDefinedResult,
    rt: &Runtime,
) -> JsonValue {
    match f {
        FailToVerifySetOperatorObjWellDefinedResult::SymmetricDifference(p) => {
            node(rt, "SymmetricDifference", None, common(&p.0, rt))
        }
        FailToVerifySetOperatorObjWellDefinedResult::Union(p) => {
            node(rt, "Union", None, common(&p.0, rt))
        }
        FailToVerifySetOperatorObjWellDefinedResult::Intersect(p) => {
            node(rt, "Intersect", None, common(&p.0, rt))
        }
        FailToVerifySetOperatorObjWellDefinedResult::SetMinus(p) => {
            node(rt, "SetMinus", None, common(&p.0, rt))
        }
        FailToVerifySetOperatorObjWellDefinedResult::FamilyUnion(p) => {
            node(rt, "FamilyUnion", None, common(&p.0, rt))
        }
        FailToVerifySetOperatorObjWellDefinedResult::FamilyIntersect(p) => {
            node(rt, "FamilyIntersect", None, common(&p.0, rt))
        }
        FailToVerifySetOperatorObjWellDefinedResult::IndexUnion(p) => node(
            rt,
            "IndexUnion",
            None,
            project_leaf_fail_to_verify_index_union_obj_well_defined(p, rt),
        ),
        FailToVerifySetOperatorObjWellDefinedResult::IndexIntersect(p) => node(
            rt,
            "IndexIntersect",
            None,
            project_leaf_fail_to_verify_index_intersect_obj_well_defined(p, rt),
        ),
        FailToVerifySetOperatorObjWellDefinedResult::PowerSet(p) => {
            node(rt, "PowerSet", None, common(&p.0, rt))
        }
        FailToVerifySetOperatorObjWellDefinedResult::IndexCart(p) => node(
            rt,
            "IndexCart",
            None,
            project_leaf_fail_to_verify_index_cart_obj_well_defined(p, rt),
        ),
    }
}

fn project_fail_to_verify_set_former_obj_well_defined_result(
    f: &FailToVerifySetFormerObjWellDefinedResult,
    rt: &Runtime,
) -> JsonValue {
    match f {
        FailToVerifySetFormerObjWellDefinedResult::MatrixSet(p) => {
            node(rt, "MatrixSet", None, common(&p.0, rt))
        }
        FailToVerifySetFormerObjWellDefinedResult::ListSet(p) => {
            node(rt, "ListSet", None, common(&p.0, rt))
        }
        FailToVerifySetFormerObjWellDefinedResult::SetBuilder(p) => node(
            rt,
            "SetBuilder",
            None,
            project_leaf_fail_to_verify_set_builder_obj_well_defined(p, rt),
        ),
        FailToVerifySetFormerObjWellDefinedResult::Range(p) => {
            node(rt, "Range", None, common(&p.0, rt))
        }
        FailToVerifySetFormerObjWellDefinedResult::ClosedRange(p) => {
            node(rt, "ClosedRange", None, common(&p.0, rt))
        }
        FailToVerifySetFormerObjWellDefinedResult::FiniteSeqSet(p) => {
            node(rt, "FiniteSeqSet", None, common(&p.0, rt))
        }
        FailToVerifySetFormerObjWellDefinedResult::SeqSet(p) => {
            node(rt, "SeqSet", None, common(&p.0, rt))
        }
        FailToVerifySetFormerObjWellDefinedResult::OneSideInfinityIntervalObj(p) => {
            node(rt, "OneSideInfinityIntervalObj", None, common(&p.0, rt))
        }
        FailToVerifySetFormerObjWellDefinedResult::IntervalObj(p) => {
            node(rt, "IntervalObj", None, common(&p.0, rt))
        }
    }
}

fn project_fail_to_verify_product_shape_obj_well_defined_result(
    f: &FailToVerifyProductShapeObjWellDefinedResult,
    rt: &Runtime,
) -> JsonValue {
    match f {
        FailToVerifyProductShapeObjWellDefinedResult::Cart(p) => {
            node(rt, "Cart", None, common(&p.0, rt))
        }
        FailToVerifyProductShapeObjWellDefinedResult::Tuple(p) => {
            node(rt, "Tuple", None, common(&p.0, rt))
        }
    }
}

fn project_fail_to_verify_function_space_obj_well_defined_result(
    f: &FailToVerifyFunctionSpaceObjWellDefinedResult,
    rt: &Runtime,
) -> JsonValue {
    match f {
        FailToVerifyFunctionSpaceObjWellDefinedResult::FnSet(p) => node(
            rt,
            "FnSet",
            None,
            project_leaf_fail_to_verify_fn_set_obj_well_defined(p, rt),
        ),
        FailToVerifyFunctionSpaceObjWellDefinedResult::AnonymousFn(p) => node(
            rt,
            "AnonymousFn",
            None,
            project_leaf_fail_to_verify_anonymous_fn_obj_well_defined(p, rt),
        ),
        FailToVerifyFunctionSpaceObjWellDefinedResult::Composition(p) => {
            node(rt, "Composition", None, super::composition::failure(p, rt))
        }
        FailToVerifyFunctionSpaceObjWellDefinedResult::Preimage(p) => node(
            rt,
            "Preimage",
            None,
            match p {
                FailToVerifyPreimageObjWellDefined::Domain(failed) => common(failed, rt),
                FailToVerifyPreimageObjWellDefined::Construction(failed) => {
                    project_preimage_construction_failure(failed, rt)
                }
            },
        ),
        FailToVerifyFunctionSpaceObjWellDefinedResult::PreimageSet(p) => node(
            rt,
            "PreimageSet",
            None,
            match p {
                FailToVerifyPreimageSetObjWellDefined::Domain(failed) => common(failed, rt),
                FailToVerifyPreimageSetObjWellDefined::Construction(failed) => {
                    project_preimage_construction_failure(failed, rt)
                }
            },
        ),
        FailToVerifyFunctionSpaceObjWellDefinedResult::FnRange(p) => node(
            rt,
            "FnRange",
            None,
            project_leaf_fail_to_verify_fn_range_obj_well_defined(p, rt),
        ),
    }
}

fn project_fail_to_verify_iterated_operator_obj_well_defined_result(
    f: &FailToVerifyIteratedOperatorObjWellDefinedResult,
    rt: &Runtime,
) -> JsonValue {
    match f {
        FailToVerifyIteratedOperatorObjWellDefinedResult::Sum(p) => {
            node(rt, "Sum", None, common(&p.0, rt))
        }
        FailToVerifyIteratedOperatorObjWellDefinedResult::SumOfFiniteSet(p) => {
            node(rt, "SumOfFiniteSet", None, common(&p.0, rt))
        }
        FailToVerifyIteratedOperatorObjWellDefinedResult::Product(p) => {
            node(rt, "Product", None, common(&p.0, rt))
        }
        FailToVerifyIteratedOperatorObjWellDefinedResult::ProductOfFiniteSet(p) => {
            node(rt, "ProductOfFiniteSet", None, common(&p.0, rt))
        }
        FailToVerifyIteratedOperatorObjWellDefinedResult::Reduce(p) => {
            node(rt, "Reduce", None, common(&p.0, rt))
        }
        FailToVerifyIteratedOperatorObjWellDefinedResult::FiniteSetReduce(p) => {
            node(rt, "FiniteSetReduce", None, common(&p.0, rt))
        }
    }
}

fn project_fail_to_verify_finite_set_stat_obj_well_defined_result(
    f: &FailToVerifyFiniteSetStatObjWellDefinedResult,
    rt: &Runtime,
) -> JsonValue {
    match f {
        FailToVerifyFiniteSetStatObjWellDefinedResult::FiniteSetSize(p) => {
            node(rt, "FiniteSetSize", None, common(&p.0, rt))
        }
        FailToVerifyFiniteSetStatObjWellDefinedResult::FiniteSetMax(p) => {
            node(rt, "FiniteSetMax", None, common(&p.0, rt))
        }
        FailToVerifyFiniteSetStatObjWellDefinedResult::FiniteSetMin(p) => {
            node(rt, "FiniteSetMin", None, common(&p.0, rt))
        }
    }
}

fn project_fail_to_verify_structish_obj_well_defined_result(
    f: &FailToVerifyStructishObjWellDefinedResult,
    rt: &Runtime,
) -> JsonValue {
    match f {
        FailToVerifyStructishObjWellDefinedResult::StructObj(p) => {
            node(rt, "StructObj", None, common(&p.0, rt))
        }
        FailToVerifyStructishObjWellDefinedResult::FieldAccess(p) => {
            node(rt, "FieldAccess", None, common(&p.0, rt))
        }
    }
}

fn project_leaf_fail_to_verify_fn_obj_obj_well_defined(
    p: &FailToVerifyFnObjObjWellDefined,
    rt: &Runtime,
) -> JsonValue {
    let projected = match p {
        FailToVerifyFnObjObjWellDefined::NotInFunctionSet => {
            message(rt, "no matching function signature")
        }
        FailToVerifyFnObjObjWellDefined::Domain(p) => common(p, rt),
        FailToVerifyFnObjObjWellDefined::Candidate(p) => {
            let failure = if let Some((index, obj, reason)) = p.stages.failed_child() {
                node(
                    rt,
                    "child",
                    Some(index),
                    super::wd::project_failed_obj(obj, reason, rt),
                )
            } else if let Some((index, requirement)) = p.stages.failed_requirement() {
                node(
                    rt,
                    "requirement",
                    Some(index),
                    project_verify_fact(requirement, rt),
                )
            } else {
                message(
                    rt,
                    "function signature arity or return shape does not match",
                )
            };
            let mut fields = vec![("failure", failure)];
            if let Some(stages) = p.stages.detailed_stages() {
                fields.push((
                    "argument_scope",
                    super::wd_by_def::project_fn_argument_scope(&p.scope, rt),
                ));
                fields.push((
                    "child_obj_well_defined",
                    JsonValue::Array(
                        stages
                            .child_obj_well_defined
                            .iter()
                            .map(|child| super::wd::project_verify_obj_wd(child, rt))
                            .collect(),
                    ),
                ));
                fields.push((
                    "requirement_fact_verified",
                    super::store::project_verify_facts(&stages.requirement_fact_verified, rt),
                ));
            }
            object_for(rt, fields)
        }
    };
    crate::json_output::helper::inherit_failure_field(rt, projected, "failure")
}

fn project_leaf_fail_to_verify_index_union_obj_well_defined(
    p: &FailToVerifyIndexUnionObjWellDefined,
    rt: &Runtime,
) -> JsonValue {
    let projected = match p {
        FailToVerifyIndexUnionObjWellDefined::NotInFunctionSet => {
            message(rt, "no matching function signature")
        }
        FailToVerifyIndexUnionObjWellDefined::Domain(p) => common(p, rt),
    };
    crate::json_output::helper::inherit_failure_field(rt, projected, "failure")
}

fn project_leaf_fail_to_verify_index_intersect_obj_well_defined(
    p: &FailToVerifyIndexIntersectObjWellDefined,
    rt: &Runtime,
) -> JsonValue {
    let projected = match p {
        FailToVerifyIndexIntersectObjWellDefined::NotInFunctionSet => {
            message(rt, "no matching function signature")
        }
        FailToVerifyIndexIntersectObjWellDefined::Domain(p) => common(p, rt),
    };
    crate::json_output::helper::inherit_failure_field(rt, projected, "failure")
}

fn project_leaf_fail_to_verify_index_cart_obj_well_defined(
    p: &FailToVerifyIndexCartObjWellDefined,
    rt: &Runtime,
) -> JsonValue {
    let projected = match p {
        FailToVerifyIndexCartObjWellDefined::NotInFunctionSet => {
            message(rt, "no matching function signature")
        }
        FailToVerifyIndexCartObjWellDefined::Domain(p) => common(p, rt),
    };
    crate::json_output::helper::inherit_failure_field(rt, projected, "failure")
}

fn project_leaf_fail_to_verify_fn_range_obj_well_defined(
    p: &FailToVerifyFnRangeObjWellDefined,
    rt: &Runtime,
) -> JsonValue {
    let projected = match p {
        FailToVerifyFnRangeObjWellDefined::NotInFunctionSet => {
            message(rt, "no matching function signature")
        }
        FailToVerifyFnRangeObjWellDefined::Domain(p) => common(p, rt),
    };
    crate::json_output::helper::inherit_failure_field(rt, projected, "failure")
}

fn project_leaf_fail_to_verify_standard_set_obj_well_defined(
    p: &FailToVerifyStandardSetObjWellDefined,
    rt: &Runtime,
) -> JsonValue {
    let projected = match p {
        FailToVerifyStandardSetObjWellDefined::Others(text) => message(rt, text),
    };
    crate::json_output::helper::inherit_failure_field(rt, projected, "failure")
}

fn project_leaf_fail_to_verify_number_obj_well_defined(
    p: &FailToVerifyNumberObjWellDefined,
    rt: &Runtime,
) -> JsonValue {
    let projected = match p {
        FailToVerifyNumberObjWellDefined::Others(text) => message(rt, text),
    };
    crate::json_output::helper::inherit_failure_field(rt, projected, "failure")
}

fn project_leaf_fail_to_verify_imaginary_unit_obj_well_defined(
    p: &FailToVerifyImaginaryUnitObjWellDefined,
    rt: &Runtime,
) -> JsonValue {
    let projected = match p {
        FailToVerifyImaginaryUnitObjWellDefined::Others(text) => message(rt, text),
    };
    crate::json_output::helper::inherit_failure_field(rt, projected, "failure")
}

fn project_leaf_fail_to_verify_euler_number_obj_well_defined(
    p: &FailToVerifyEulerNumberObjWellDefined,
    rt: &Runtime,
) -> JsonValue {
    let projected = match p {
        FailToVerifyEulerNumberObjWellDefined::Others(text) => message(rt, text),
    };
    crate::json_output::helper::inherit_failure_field(rt, projected, "failure")
}

fn project_leaf_fail_to_verify_pi_obj_well_defined(
    p: &FailToVerifyPiObjWellDefined,
    rt: &Runtime,
) -> JsonValue {
    let projected = match p {
        FailToVerifyPiObjWellDefined::Others(text) => message(rt, text),
    };
    crate::json_output::helper::inherit_failure_field(rt, projected, "failure")
}

fn project_leaf_fail_to_verify_identifier_obj_well_defined(
    p: &FailToVerifyIdentifierObjWellDefined,
    rt: &Runtime,
) -> JsonValue {
    let projected = match p {
        FailToVerifyIdentifierObjWellDefined::Undefined { obj } => object_for(
            rt,
            vec![
                ("phase", string("undefined")),
                ("obj", string(obj.readable_string())),
            ],
        ),
        FailToVerifyIdentifierObjWellDefined::Others(text) => message(rt, text),
    };
    crate::json_output::helper::inherit_failure_field(rt, projected, "failure")
}
fn project_leaf_fail_to_verify_set_builder_obj_well_defined(
    p: &FailToVerifySetBuilderObjWellDefined,
    rt: &Runtime,
) -> JsonValue {
    let projected = match p {
        FailToVerifySetBuilderObjWellDefined::ParamSet { obj, failed } => object_for(
            rt,
            vec![
                ("phase", string("parameter_set")),
                ("obj", string(obj.readable_string())),
                ("failure", project_obj_wd_failure(failed, rt)),
            ],
        ),
        FailToVerifySetBuilderObjWellDefined::Fact {
            failed_index,
            failed,
            ..
        } => node(
            rt,
            "fact",
            Some(*failed_index),
            project_fact_wd_failure(failed, rt),
        ),
        FailToVerifySetBuilderObjWellDefined::Others(text) => message(rt, text),
    };
    crate::json_output::helper::inherit_failure_field(rt, projected, "failure")
}

fn project_leaf_fail_to_verify_fn_set_obj_well_defined(
    p: &FailToVerifyFnSetObjWellDefined,
    rt: &Runtime,
) -> JsonValue {
    let projected = match p {
        FailToVerifyFnSetObjWellDefined::ParamTypeCitesEarlierBinder { failed_index } => {
            object_for(
                rt,
                vec![
                    ("phase", string("parameter_dependency")),
                    ("index", JsonValue::Number(*failed_index as f64)),
                ],
            )
        }
        FailToVerifyFnSetObjWellDefined::ParamType {
            failed_index,
            failed_obj,
            failed,
            ..
        } => object_for(
            rt,
            vec![
                ("phase", string("parameter_type")),
                ("index", JsonValue::Number(*failed_index as f64)),
                ("obj", string(failed_obj.readable_string())),
                ("failure", project_obj_wd_failure(failed, rt)),
            ],
        ),
        FailToVerifyFnSetObjWellDefined::DomFact {
            failed_index,
            failed_dom,
            ..
        } => node(
            rt,
            "domain_fact",
            Some(*failed_index),
            project_fact_wd_failure(failed_dom, rt),
        ),
        FailToVerifyFnSetObjWellDefined::RetSet {
            failed_obj, failed, ..
        } => object_for(
            rt,
            vec![
                ("phase", string("return_set")),
                ("obj", string(failed_obj.readable_string())),
                ("failure", project_obj_wd_failure(failed, rt)),
            ],
        ),
        FailToVerifyFnSetObjWellDefined::Others(text) => message(rt, text),
    };
    crate::json_output::helper::inherit_failure_field(rt, projected, "failure")
}

fn project_leaf_fail_to_verify_anonymous_fn_obj_well_defined(
    p: &FailToVerifyAnonymousFnObjWellDefined,
    rt: &Runtime,
) -> JsonValue {
    let projected = match p {
        FailToVerifyAnonymousFnObjWellDefined::ParamTypeCitesEarlierBinder { failed_index } => {
            object_for(
                rt,
                vec![
                    ("phase", string("parameter_dependency")),
                    ("index", JsonValue::Number(*failed_index as f64)),
                ],
            )
        }
        FailToVerifyAnonymousFnObjWellDefined::ParamType {
            failed_index,
            failed_obj,
            failed,
            ..
        } => object_for(
            rt,
            vec![
                ("phase", string("parameter_type")),
                ("index", JsonValue::Number(*failed_index as f64)),
                ("obj", string(failed_obj.readable_string())),
                ("failure", project_obj_wd_failure(failed, rt)),
            ],
        ),
        FailToVerifyAnonymousFnObjWellDefined::DomFact {
            failed_index,
            failed_dom,
            ..
        } => node(
            rt,
            "domain_fact",
            Some(*failed_index),
            project_fact_wd_failure(failed_dom, rt),
        ),
        FailToVerifyAnonymousFnObjWellDefined::RetSet {
            failed_obj, failed, ..
        } => object_for(
            rt,
            vec![
                ("phase", string("return_set")),
                ("obj", string(failed_obj.readable_string())),
                ("failure", project_obj_wd_failure(failed, rt)),
            ],
        ),
        FailToVerifyAnonymousFnObjWellDefined::Body {
            failed_obj, failed, ..
        } => object_for(
            rt,
            vec![
                ("phase", string("body")),
                ("obj", string(failed_obj.readable_string())),
                ("failure", project_obj_wd_failure(failed, rt)),
            ],
        ),
        FailToVerifyAnonymousFnObjWellDefined::BodyInRetSet { failed, .. } => node(
            rt,
            "body_in_return_set",
            None,
            project_verify_fact(failed, rt),
        ),
        FailToVerifyAnonymousFnObjWellDefined::Others(text) => message(rt, text),
    };
    crate::json_output::helper::inherit_failure_field(rt, projected, "failure")
}

fn project_preimage_construction_failure(
    failed: &crate::execute::execute_fact_stmt::function_preimage::FunctionPreimageConstructionFailure,
    rt: &Runtime,
) -> JsonValue {
    use crate::execute::execute_fact_stmt::function_preimage::FunctionPreimageConstructionFailure;
    match failed {
        FunctionPreimageConstructionFailure::NoCompleteDomain => {
            message(rt, "preimage requires a checked complete function domain")
        }
        FunctionPreimageConstructionFailure::Construction(failures) => object_for(
            rt,
            vec![(
                "bounded_subset_failures",
                JsonValue::Array(
                    failures
                        .iter()
                        .map(|failure| super::wd::project_verify_obj_wd(failure, rt))
                        .collect(),
                ),
            )],
        ),
    }
}

pub(super) fn project_or_wd_failure(
    failure: &crate::execute::execute_fact_stmt::FailToVerifyOrFactWellDefinedResult,
    rt: &Runtime,
) -> JsonValue {
    node(
        rt,
        "branch",
        Some(failure.failed_index),
        project_fact_wd_failure(&failure.failed_branch, rt),
    )
}

fn with_fact(rt: &Runtime, mut value: JsonValue, fact: crate::ast::fact::Fact) -> JsonValue {
    if let JsonValue::Object(fields) = &mut value {
        fields.insert(
            crate::json_output::json_keys::localize_key(
                "fact",
                rt.launch_command.output_language(),
            ),
            string(fact.readable_string()),
        );
    }
    value
}
