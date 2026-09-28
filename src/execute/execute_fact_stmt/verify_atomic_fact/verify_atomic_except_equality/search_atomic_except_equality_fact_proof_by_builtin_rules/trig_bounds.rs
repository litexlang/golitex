use crate::ast::obj::{Number, Obj, Literal, TrigOperator};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_inverse_trig::{
    half_pi, negative_half_pi, objs_match_half_pi_bound, pi_obj, zero_obj,
};
use crate::rational_expression::objs_equal_by_rational_expression_evaluation;

// Match `lower <= arcsin(x)` where lower is rationally `-pi/2`.
pub(crate) fn match_arcsin_principal_lower(left: &Obj, right: &Obj) -> bool {
    matches!(right, Obj::TrigOperator(TrigOperator::Arcsin(_))) && objs_match_half_pi_bound(left, &negative_half_pi())
}

// Match `arcsin(x) <= upper` where upper is rationally `pi/2`.
pub(crate) fn match_arcsin_principal_upper(left: &Obj, right: &Obj) -> bool {
    matches!(left, Obj::TrigOperator(TrigOperator::Arcsin(_))) && objs_match_half_pi_bound(right, &half_pi())
}

// Match `0 <= arccos(x)`.
pub(crate) fn match_arccos_principal_lower(left: &Obj, right: &Obj) -> bool {
    matches!(right, Obj::TrigOperator(TrigOperator::Arccos(_))) && objs_equal_by_rational_expression_evaluation(left, &zero_obj())
}

// Match `arccos(x) <= pi`.
pub(crate) fn match_arccos_principal_upper(left: &Obj, right: &Obj) -> bool {
    matches!(left, Obj::TrigOperator(TrigOperator::Arccos(_))) && objs_match_half_pi_bound(right, &pi_obj())
}

// Match `-1 <= sin(x)` or `-1 <= cos(x)`.
pub(crate) fn match_unit_circle_lower(left: &Obj, right: &Obj) -> bool {
    is_neg_one(left) && matches!(right, Obj::TrigOperator(TrigOperator::Sin(_)) | Obj::TrigOperator(TrigOperator::Cos(_)))
}

// Match `sin(x) <= 1` or `cos(x) <= 1`.
pub(crate) fn match_unit_circle_upper(left: &Obj, right: &Obj) -> bool {
    is_one(right) && matches!(left, Obj::TrigOperator(TrigOperator::Sin(_)) | Obj::TrigOperator(TrigOperator::Cos(_)))
}

// Match `-pi/2 < arctan(x)`.
pub(crate) fn match_arctan_principal_lower(left: &Obj, right: &Obj) -> bool {
    matches!(right, Obj::TrigOperator(TrigOperator::Arctan(_))) && objs_match_half_pi_bound(left, &negative_half_pi())
}

// Match `arctan(x) < pi/2`.
pub(crate) fn match_arctan_principal_upper(left: &Obj, right: &Obj) -> bool {
    matches!(left, Obj::TrigOperator(TrigOperator::Arctan(_))) && objs_match_half_pi_bound(right, &half_pi())
}

// Match `0 < arccot(x)`.
pub(crate) fn match_arccot_principal_lower(left: &Obj, right: &Obj) -> bool {
    matches!(right, Obj::TrigOperator(TrigOperator::Arccot(_)))
        && objs_equal_by_rational_expression_evaluation(left, &zero_obj())
}

// Match `arccot(x) < pi`.
pub(crate) fn match_arccot_principal_upper(left: &Obj, right: &Obj) -> bool {
    matches!(left, Obj::TrigOperator(TrigOperator::Arccot(_))) && objs_match_half_pi_bound(right, &pi_obj())
}

fn is_neg_one(obj: &Obj) -> bool {
    matches!(
        obj,
        Obj::Literal(Literal::Number(Number {
            normalized_value,
        })) if normalized_value == "-1"
    ) || objs_equal_by_rational_expression_evaluation(
        obj,
        &Obj::Literal(Literal::Number(Number {
            normalized_value: "-1".to_string(),
        })),
    )
}

fn is_one(obj: &Obj) -> bool {
    matches!(
        obj,
        Obj::Literal(Literal::Number(Number {
            normalized_value,
        })) if normalized_value == "1"
    )
}
