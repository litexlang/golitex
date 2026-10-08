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
    object_for(rt, entries)
}
fn message(rt: &Runtime, text: &str) -> JsonValue {
    object_for(rt, vec![("message", string(text))])
}

pub(super) fn project_fact_wd_failure(
    f: &FailToVerifyFactWellDefinedResult,
    rt: &Runtime,
) -> JsonValue {
    use FailToVerifyFactWellDefinedResult::*;
    match f {
        Equality(p) => project_obj_wd_failure(&p.reason, rt),
        AtomicExceptEquality(p) => project_atomic_wd_failure(p, rt),
        AndFact(p) => node(rt, "component", Some(p.failed_index), project_atomic_wd_failure(&p.failed_component, rt)),
        ChainFact(p) => node(rt, "adjacent", Some(p.failed_index), project_atomic_wd_failure(&p.failed_adjacent, rt)),
        OrFact(p) => node(rt, "branch", Some(p.failed_index), project_fact_wd_failure(&p.failed_branch, rt)),
        ExistFact(p) => project_exist_wd_failure(p, rt),
        ForallFact(p) => project_forall_wd_failure(p, rt),
        ForallFactWithIff(p) => match p {
            crate::execute::execute_fact_stmt::verify_forall_fact_with_iff::FailToVerifyForallFactWithIffWellDefinedResult::ParamType(p) => node(rt, "parameter_type", None, project_obj_wd_failure(p, rt)),
            crate::execute::execute_fact_stmt::verify_forall_fact_with_iff::FailToVerifyForallFactWithIffWellDefinedResult::DomFact { failed_index, failed_dom, .. } => node(rt, "failed_dom", Some(*failed_index), project_fact_wd_failure(failed_dom, rt)),
            crate::execute::execute_fact_stmt::verify_forall_fact_with_iff::FailToVerifyForallFactWithIffWellDefinedResult::ThenFact { failed_index, failed_then, .. } => node(rt, "failed_then", Some(*failed_index), project_fact_wd_failure(failed_then, rt)),
            crate::execute::execute_fact_stmt::verify_forall_fact_with_iff::FailToVerifyForallFactWithIffWellDefinedResult::IffFact { failed_index, failed_iff, .. } => node(rt, "failed_iff", Some(*failed_index), project_fact_wd_failure(failed_iff, rt)),
        },
        NotForall(p) => match p {
            crate::execute::execute_fact_stmt::verify_not_forall_fact::FailToVerifyNotForallFactWellDefinedResult::ParamType(p) => node(rt, "parameter_type", None, project_obj_wd_failure(p, rt)),
            crate::execute::execute_fact_stmt::verify_not_forall_fact::FailToVerifyNotForallFactWellDefinedResult::DomFact { failed_index, failed_dom, .. } => node(rt, "failed_dom", Some(*failed_index), project_fact_wd_failure(failed_dom, rt)),
            crate::execute::execute_fact_stmt::verify_not_forall_fact::FailToVerifyNotForallFactWellDefinedResult::ThenFact { failed_index, failed_then, .. } => node(rt, "failed_then", Some(*failed_index), project_fact_wd_failure(failed_then, rt)),
        },
    }
}

pub(super) fn project_exist_wd_failure(
    failure: &crate::execute::execute_fact_stmt::verify_exist_shaped_fact::FailToVerifyExistShapedFactWellDefinedResult,
    rt: &Runtime,
) -> JsonValue {
    use crate::execute::execute_fact_stmt::verify_exist_shaped_fact::FailToVerifyExistShapedFactWellDefinedResult;
    match failure {
        FailToVerifyExistShapedFactWellDefinedResult::ParamType(failed) => node(
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
    }
}

pub(super) fn project_forall_wd_failure(
    failure: &crate::execute::execute_fact_stmt::verify_forall_fact::FailToVerifyForallFactWellDefinedResult,
    rt: &Runtime,
) -> JsonValue {
    use crate::execute::execute_fact_stmt::verify_forall_fact::FailToVerifyForallFactWellDefinedResult::*;
    match failure {
        ParamType(p) => node(rt, "parameter_type", None, project_obj_wd_failure(p, rt)),
        AutoOpenStructLayer(_) => message(rt, "failed to open struct carrier"),
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
    }
}

pub(super) fn project_atomic_wd_failure(
    failure: &crate::execute::execute_fact_stmt::verify_atomic_fact::FailToVerifyAtomicFactWellDefinedResult,
    rt: &Runtime,
) -> JsonValue {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::{
        FailToVerifyAtomicFactWellDefinedResult, PredicateSignatureWellDefinedFailure,
    };
    match failure {
        FailToVerifyAtomicFactWellDefinedResult::Argument(reason) => {
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
    }
}

fn common(f: &FailToVerifyObjWellDefinedByDefCommon, rt: &Runtime) -> JsonValue {
    match f {
        FailToVerifyObjWellDefinedByDefCommon::Child { obj, child } => object_for(
            rt,
            vec![
                ("phase", string("child")),
                ("obj", string(obj.readable_string())),
                ("failure", project_obj_wd_failure(child, rt)),
            ],
        ),
        FailToVerifyObjWellDefinedByDefCommon::Requirement { obj, result } => object_for(
            rt,
            vec![
                ("phase", string("requirement")),
                ("obj", string(obj.readable_string())),
                ("result", project_verify_fact(result, rt)),
            ],
        ),
        FailToVerifyObjWellDefinedByDefCommon::Others(text) => message(rt, text),
    }
}

pub(super) fn project_obj_wd_failure(
    f: &FailToVerifyObjWellDefinedResult,
    rt: &Runtime,
) -> JsonValue {
    match f {
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
    }
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
    match p {
        FailToVerifyFnObjObjWellDefined::NotInFunctionSet => {
            message(rt, "no matching function signature")
        }
        FailToVerifyFnObjObjWellDefined::Domain(p) => common(p, rt),
    }
}

fn project_leaf_fail_to_verify_index_union_obj_well_defined(
    p: &FailToVerifyIndexUnionObjWellDefined,
    rt: &Runtime,
) -> JsonValue {
    match p {
        FailToVerifyIndexUnionObjWellDefined::NotInFunctionSet => {
            message(rt, "no matching function signature")
        }
        FailToVerifyIndexUnionObjWellDefined::Domain(p) => common(p, rt),
    }
}

fn project_leaf_fail_to_verify_index_intersect_obj_well_defined(
    p: &FailToVerifyIndexIntersectObjWellDefined,
    rt: &Runtime,
) -> JsonValue {
    match p {
        FailToVerifyIndexIntersectObjWellDefined::NotInFunctionSet => {
            message(rt, "no matching function signature")
        }
        FailToVerifyIndexIntersectObjWellDefined::Domain(p) => common(p, rt),
    }
}

fn project_leaf_fail_to_verify_index_cart_obj_well_defined(
    p: &FailToVerifyIndexCartObjWellDefined,
    rt: &Runtime,
) -> JsonValue {
    match p {
        FailToVerifyIndexCartObjWellDefined::NotInFunctionSet => {
            message(rt, "no matching function signature")
        }
        FailToVerifyIndexCartObjWellDefined::Domain(p) => common(p, rt),
    }
}

fn project_leaf_fail_to_verify_fn_range_obj_well_defined(
    p: &FailToVerifyFnRangeObjWellDefined,
    rt: &Runtime,
) -> JsonValue {
    match p {
        FailToVerifyFnRangeObjWellDefined::NotInFunctionSet => {
            message(rt, "no matching function signature")
        }
        FailToVerifyFnRangeObjWellDefined::Domain(p) => common(p, rt),
    }
}

fn project_leaf_fail_to_verify_standard_set_obj_well_defined(
    p: &FailToVerifyStandardSetObjWellDefined,
    rt: &Runtime,
) -> JsonValue {
    match p {
        FailToVerifyStandardSetObjWellDefined::Others(text) => message(rt, text),
    }
}

fn project_leaf_fail_to_verify_number_obj_well_defined(
    p: &FailToVerifyNumberObjWellDefined,
    rt: &Runtime,
) -> JsonValue {
    match p {
        FailToVerifyNumberObjWellDefined::Others(text) => message(rt, text),
    }
}

fn project_leaf_fail_to_verify_imaginary_unit_obj_well_defined(
    p: &FailToVerifyImaginaryUnitObjWellDefined,
    rt: &Runtime,
) -> JsonValue {
    match p {
        FailToVerifyImaginaryUnitObjWellDefined::Others(text) => message(rt, text),
    }
}

fn project_leaf_fail_to_verify_euler_number_obj_well_defined(
    p: &FailToVerifyEulerNumberObjWellDefined,
    rt: &Runtime,
) -> JsonValue {
    match p {
        FailToVerifyEulerNumberObjWellDefined::Others(text) => message(rt, text),
    }
}

fn project_leaf_fail_to_verify_pi_obj_well_defined(
    p: &FailToVerifyPiObjWellDefined,
    rt: &Runtime,
) -> JsonValue {
    match p {
        FailToVerifyPiObjWellDefined::Others(text) => message(rt, text),
    }
}

fn project_leaf_fail_to_verify_identifier_obj_well_defined(
    p: &FailToVerifyIdentifierObjWellDefined,
    rt: &Runtime,
) -> JsonValue {
    match p {
        FailToVerifyIdentifierObjWellDefined::Undefined { obj } => object_for(
            rt,
            vec![
                ("phase", string("undefined")),
                ("obj", string(obj.readable_string())),
            ],
        ),
        FailToVerifyIdentifierObjWellDefined::Others(text) => message(rt, text),
    }
}
fn project_leaf_fail_to_verify_set_builder_obj_well_defined(
    p: &FailToVerifySetBuilderObjWellDefined,
    rt: &Runtime,
) -> JsonValue {
    match p {
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
    }
}

fn project_leaf_fail_to_verify_fn_set_obj_well_defined(
    p: &FailToVerifyFnSetObjWellDefined,
    rt: &Runtime,
) -> JsonValue {
    match p {
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
    }
}

fn project_leaf_fail_to_verify_anonymous_fn_obj_well_defined(
    p: &FailToVerifyAnonymousFnObjWellDefined,
    rt: &Runtime,
) -> JsonValue {
    match p {
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
    }
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
