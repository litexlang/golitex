//! Generated atomic-except-equality builtin-rule detailed projection.
use super::store::project_verify_facts;
use super::verify::project_verify_fact;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules as br;
use br::AtomicExceptEqualityFactSearchProofByBuiltinRule;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::search_atomic_except_equality_fact_proof_by_builtin_rule_result::{
    CoprimeFactSearchProofByBuiltinRule, NotCoprimeFactSearchProofByBuiltinRule,
    NotPrimeFactSearchProofByBuiltinRule, PrimeFactSearchProofByBuiltinRule,
};
use crate::json_output::helper::{object_for, string};
use crate::knowledge_base::JsonValue;
use crate::runtime::Runtime;

pub(super) fn project_atomic_builtin_rule(
    proof: &AtomicExceptEqualityFactSearchProofByBuiltinRule,
    runtime: &Runtime,
) -> JsonValue {
    match proof {
        AtomicExceptEqualityFactSearchProofByBuiltinRule::PrimeFact(PrimeFactSearchProofByBuiltinRule::PrimeByComputation(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("PrimeFact")),
                ("rule", string("PrimeByComputation")),
            ];
            entries.push(("resolved_value", string(p.resolved_value.clone())));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::CoprimeFact(CoprimeFactSearchProofByBuiltinRule::CoprimeByComputation(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("CoprimeFact")),
                ("rule", string("CoprimeByComputation")),
            ];
            entries.push(("left_resolved", string(p.left_resolved.clone())));
            entries.push(("right_resolved", string(p.right_resolved.clone())));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(br::less::LessFactSearchProofByBuiltinRule::ClosedNumericComparison(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessFact")),
                ("rule", string("ClosedNumericComparison")),
            ];
            entries.push(("left_normal", string(p.left_normal.clone())));
            entries.push(("right_normal", string(p.right_normal.clone())));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(br::less::LessFactSearchProofByBuiltinRule::SubtractOneLess(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessFact")),
                ("rule", string("SubtractOneLess")),
            ];
            entries.push(("minuend", string(p.minuend.readable_string())));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(br::less::LessFactSearchProofByBuiltinRule::ArctanPrincipalLowerBound(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessFact")),
                ("rule", string("ArctanPrincipalLowerBound")),
            ];
            let _ = p;
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(br::less::LessFactSearchProofByBuiltinRule::ArctanPrincipalUpperBound(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessFact")),
                ("rule", string("ArctanPrincipalUpperBound")),
            ];
            let _ = p;
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(br::less::LessFactSearchProofByBuiltinRule::ArccotPrincipalLowerBound(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessFact")),
                ("rule", string("ArccotPrincipalLowerBound")),
            ];
            let _ = p;
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(br::less::LessFactSearchProofByBuiltinRule::ArccotPrincipalUpperBound(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessFact")),
                ("rule", string("ArccotPrincipalUpperBound")),
            ];
            let _ = p;
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(br::less::LessFactSearchProofByBuiltinRule::SumBothPositive(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessFact")),
                ("rule", string("SumBothPositive")),
            ];
            entries.push(("left_positive_proof", project_verify_fact(&p.left_positive_proof, runtime)));
            entries.push(("right_positive_proof", project_verify_fact(&p.right_positive_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(br::less::LessFactSearchProofByBuiltinRule::SumLeftStrictRightNonnegative(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessFact")),
                ("rule", string("SumLeftStrictRightNonnegative")),
            ];
            entries.push(("left_positive_proof", project_verify_fact(&p.left_positive_proof, runtime)));
            entries.push(("right_nonnegative_proof", project_verify_fact(&p.right_nonnegative_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(br::less::LessFactSearchProofByBuiltinRule::SumLeftNonnegativeRightStrict(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessFact")),
                ("rule", string("SumLeftNonnegativeRightStrict")),
            ];
            entries.push(("left_nonnegative_proof", project_verify_fact(&p.left_nonnegative_proof, runtime)));
            entries.push(("right_positive_proof", project_verify_fact(&p.right_positive_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(br::less::LessFactSearchProofByBuiltinRule::ProductBothPositive(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessFact")),
                ("rule", string("ProductBothPositive")),
            ];
            entries.push(("left_positive_proof", project_verify_fact(&p.left_positive_proof, runtime)));
            entries.push(("right_positive_proof", project_verify_fact(&p.right_positive_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(br::less::LessFactSearchProofByBuiltinRule::EvenPowPositiveFromNonzero(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessFact")),
                ("rule", string("EvenPowPositiveFromNonzero")),
            ];
            entries.push(("base_nonzero_proof", project_verify_fact(&p.base_nonzero_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(br::less::LessFactSearchProofByBuiltinRule::PowPositiveFromPositiveBase(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessFact")),
                ("rule", string("PowPositiveFromPositiveBase")),
            ];
            entries.push(("base_positive_proof", project_verify_fact(&p.base_positive_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(br::less::LessFactSearchProofByBuiltinRule::SqrtPositive(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessFact")),
                ("rule", string("SqrtPositive")),
            ];
            entries.push(("arg_positive_proof", project_verify_fact(&p.arg_positive_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(br::less::LessFactSearchProofByBuiltinRule::SqrtMonotoneIncreasing(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessFact")),
                ("rule", string("SqrtMonotoneIncreasing")),
            ];
            entries.push(("left_nonnegative_proof", project_verify_fact(&p.left_nonnegative_proof, runtime)));
            entries.push(("right_nonnegative_proof", project_verify_fact(&p.right_nonnegative_proof, runtime)));
            entries.push(("args_order_proof", project_verify_fact(&p.args_order_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(br::less::LessFactSearchProofByBuiltinRule::LogOrderPreservingStrict(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessFact")),
                ("rule", string("LogOrderPreservingStrict")),
            ];
            entries.push(("base_gt_one_proof", project_verify_fact(&p.base_gt_one_proof, runtime)));
            entries.push(("left_arg_positive_proof", project_verify_fact(&p.left_arg_positive_proof, runtime)));
            entries.push(("right_arg_positive_proof", project_verify_fact(&p.right_arg_positive_proof, runtime)));
            entries.push(("args_order_proof", project_verify_fact(&p.args_order_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(br::less::LessFactSearchProofByBuiltinRule::LogPositiveFromBaseAndArgGtOne(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessFact")),
                ("rule", string("LogPositiveFromBaseAndArgGtOne")),
            ];
            entries.push(("base_gt_one_proof", project_verify_fact(&p.base_gt_one_proof, runtime)));
            entries.push(("arg_gt_one_proof", project_verify_fact(&p.arg_gt_one_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(br::less::LessFactSearchProofByBuiltinRule::LogNegativeFromBaseGtOneArgInUnitInterval(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessFact")),
                ("rule", string("LogNegativeFromBaseGtOneArgInUnitInterval")),
            ];
            entries.push(("base_gt_one_proof", project_verify_fact(&p.base_gt_one_proof, runtime)));
            entries.push(("arg_positive_proof", project_verify_fact(&p.arg_positive_proof, runtime)));
            entries.push(("arg_lt_one_proof", project_verify_fact(&p.arg_lt_one_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(br::less::LessFactSearchProofByBuiltinRule::LessTransitivity(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessFact")),
                ("rule", string("LessTransitivity")),
            ];
            entries.push(("cite_fact_id", string(p.left_to_mid_cite_fact_id.to_string())));
            if let Some(fact) = runtime.fact_by_id_in_stack(p.left_to_mid_cite_fact_id) {
                entries.push(("cite", string(fact.readable_string())));
            }
            entries.push(("cite_fact_id", string(p.mid_to_right_cite_fact_id.to_string())));
            if let Some(fact) = runtime.fact_by_id_in_stack(p.mid_to_right_cite_fact_id) {
                entries.push(("cite", string(fact.readable_string())));
            }
            entries.push(("left_to_mid_strict", JsonValue::Bool(p.left_to_mid_strict)));
            entries.push(("mid_to_right_strict", JsonValue::Bool(p.mid_to_right_strict)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(br::less::LessFactSearchProofByBuiltinRule::LessFromPosDifference(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessFact")),
                ("rule", string("LessFromPosDifference")),
            ];
            entries.push(("cite_fact_id", string(p.cite_fact_id.to_string())));
            if let Some(fact) = runtime.fact_by_id_in_stack(p.cite_fact_id) {
                entries.push(("cite", string(fact.readable_string())));
            }
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(br::less::LessFactSearchProofByBuiltinRule::PosDifferenceFromLess(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessFact")),
                ("rule", string("PosDifferenceFromLess")),
            ];
            entries.push(("cite_fact_id", string(p.cite_fact_id.to_string())));
            if let Some(fact) = runtime.fact_by_id_in_stack(p.cite_fact_id) {
                entries.push(("cite", string(fact.readable_string())));
            }
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(br::less::LessFactSearchProofByBuiltinRule::ModRemainderStrictUpperBound(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessFact")),
                ("rule", string("ModRemainderStrictUpperBound")),
            ];
            entries.push(("dividend_in_z_proof", project_verify_fact(&p.dividend_in_z_proof, runtime)));
            entries.push(("modulus_in_n_pos_proof", project_verify_fact(&p.modulus_in_n_pos_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(br::less::LessFactSearchProofByBuiltinRule::DivMonotoneStrictSamePosDivisor(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessFact")),
                ("rule", string("DivMonotoneStrictSamePosDivisor")),
            ];
            entries.push(("divisor_pos_proof", project_verify_fact(&p.divisor_pos_proof, runtime)));
            entries.push(("numerators_order_proof", project_verify_fact(&p.numerators_order_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(br::less::LessFactSearchProofByBuiltinRule::DivByGtOneLessSelf(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessFact")),
                ("rule", string("DivByGtOneLessSelf")),
            ];
            entries.push(("numerator_pos_proof", project_verify_fact(&p.numerator_pos_proof, runtime)));
            entries.push(("denominator_gt_one_proof", project_verify_fact(&p.denominator_gt_one_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(br::less::LessFactSearchProofByBuiltinRule::DivMonotoneStrictSameNegDivisor(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessFact")),
                ("rule", string("DivMonotoneStrictSameNegDivisor")),
            ];
            entries.push(("divisor_neg_proof", project_verify_fact(&p.divisor_neg_proof, runtime)));
            entries.push(("numerators_order_proof", project_verify_fact(&p.numerators_order_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(br::less::LessFactSearchProofByBuiltinRule::NumericLowerBoundWeakenLt(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessFact")),
                ("rule", string("NumericLowerBoundWeakenLt")),
            ];
            entries.push(("cite_fact_id", string(p.cite_fact_id.to_string())));
            if let Some(fact) = runtime.fact_by_id_in_stack(p.cite_fact_id) {
                entries.push(("cite", string(fact.readable_string())));
            }
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(br::less::LessFactSearchProofByBuiltinRule::NumericUpperBoundWeakenLt(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessFact")),
                ("rule", string("NumericUpperBoundWeakenLt")),
            ];
            entries.push(("cite_fact_id", string(p.cite_fact_id.to_string())));
            if let Some(fact) = runtime.fact_by_id_in_stack(p.cite_fact_id) {
                entries.push(("cite", string(fact.readable_string())));
            }
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(br::less::LessFactSearchProofByBuiltinRule::PositiveEvenGtOne(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessFact")),
                ("rule", string("PositiveEvenGtOne")),
            ];
            entries.push(("in_n_pos_proof", project_verify_fact(&p.in_n_pos_proof, runtime)));
            entries.push(("even_proof", project_verify_fact(&p.even_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(br::less::LessFactSearchProofByBuiltinRule::AddRightCongruenceStrict(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessFact")),
                ("rule", string("AddRightCongruenceStrict")),
            ];
            entries.push(("premise_proof", project_verify_fact(&p.premise_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(br::less::LessFactSearchProofByBuiltinRule::AddLeftCongruenceStrict(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessFact")),
                ("rule", string("AddLeftCongruenceStrict")),
            ];
            entries.push(("premise_proof", project_verify_fact(&p.premise_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(br::less::LessFactSearchProofByBuiltinRule::MulLeftPositiveMonotoneStrict(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessFact")),
                ("rule", string("MulLeftPositiveMonotoneStrict")),
            ];
            entries.push(("positive_factor_proof", project_verify_fact(&p.positive_factor_proof, runtime)));
            entries.push(("order_premise_proof", project_verify_fact(&p.order_premise_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(br::less::LessFactSearchProofByBuiltinRule::MulRightPositiveMonotoneStrict(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessFact")),
                ("rule", string("MulRightPositiveMonotoneStrict")),
            ];
            entries.push(("positive_factor_proof", project_verify_fact(&p.positive_factor_proof, runtime)));
            entries.push(("order_premise_proof", project_verify_fact(&p.order_premise_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(br::less::LessFactSearchProofByBuiltinRule::OrderSignFromPositiveLiteralBound(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessFact")),
                ("rule", string("OrderSignFromPositiveLiteralBound")),
            ];
            entries.push(("cite_fact_id", string(p.cite_fact_id.to_string())));
            if let Some(fact) = runtime.fact_by_id_in_stack(p.cite_fact_id) {
                entries.push(("cite", string(fact.readable_string())));
            }
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(br::less::LessFactSearchProofByBuiltinRule::OrderFlipMulMinusOne(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessFact")),
                ("rule", string("OrderFlipMulMinusOne")),
            ];
            entries.push(("cite_fact_id", string(p.cite_fact_id.to_string())));
            if let Some(fact) = runtime.fact_by_id_in_stack(p.cite_fact_id) {
                entries.push(("cite", string(fact.readable_string())));
            }
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterFact(br::greater::GreaterFactSearchProofByBuiltinRule::ClosedNumericComparison(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("GreaterFact")),
                ("rule", string("ClosedNumericComparison")),
            ];
            entries.push(("left_normal", string(p.left_normal.clone())));
            entries.push(("right_normal", string(p.right_normal.clone())));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterFact(br::greater::GreaterFactSearchProofByBuiltinRule::FromKnownLess(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("GreaterFact")),
                ("rule", string("FromKnownLess")),
            ];
            entries.push(("cite_fact_id", string(p.cite_fact_id.to_string())));
            if let Some(fact) = runtime.fact_by_id_in_stack(p.cite_fact_id) {
                entries.push(("cite", string(fact.readable_string())));
            }
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterFact(br::greater::GreaterFactSearchProofByBuiltinRule::AddRightCongruenceStrict(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("GreaterFact")),
                ("rule", string("AddRightCongruenceStrict")),
            ];
            entries.push(("premise_proof", project_verify_fact(&p.premise_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterFact(br::greater::GreaterFactSearchProofByBuiltinRule::AddLeftCongruenceStrict(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("GreaterFact")),
                ("rule", string("AddLeftCongruenceStrict")),
            ];
            entries.push(("premise_proof", project_verify_fact(&p.premise_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterFact(br::greater::GreaterFactSearchProofByBuiltinRule::MulLeftPositiveMonotoneStrict(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("GreaterFact")),
                ("rule", string("MulLeftPositiveMonotoneStrict")),
            ];
            entries.push(("positive_factor_proof", project_verify_fact(&p.positive_factor_proof, runtime)));
            entries.push(("order_premise_proof", project_verify_fact(&p.order_premise_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterFact(br::greater::GreaterFactSearchProofByBuiltinRule::MulRightPositiveMonotoneStrict(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("GreaterFact")),
                ("rule", string("MulRightPositiveMonotoneStrict")),
            ];
            entries.push(("positive_factor_proof", project_verify_fact(&p.positive_factor_proof, runtime)));
            entries.push(("order_premise_proof", project_verify_fact(&p.order_premise_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterFact(br::greater::GreaterFactSearchProofByBuiltinRule::FromPositiveRealMembership(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("GreaterFact")),
                ("rule", string("FromPositiveRealMembership")),
            ];
            entries.push(("membership_proof", project_verify_fact(&p.membership_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterFact(br::greater::GreaterFactSearchProofByBuiltinRule::NativeEulerGreaterZero(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("GreaterFact")),
                ("rule", string("NativeEulerGreaterZero")),
            ];
            let _ = p;
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterFact(br::greater::GreaterFactSearchProofByBuiltinRule::NativePiGreaterZero(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("GreaterFact")),
                ("rule", string("NativePiGreaterZero")),
            ];
            let _ = p;
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::ClosedNumericComparison(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessEqualFact")),
                ("rule", string("ClosedNumericComparison")),
            ];
            entries.push(("left_normal", string(p.left_normal.clone())));
            entries.push(("right_normal", string(p.right_normal.clone())));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::OrderReflexivity(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessEqualFact")),
                ("rule", string("OrderReflexivity")),
            ];
            entries.push(("repeated_object", string(p.repeated_object.readable_string())));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::FromKnownLess(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessEqualFact")),
                ("rule", string("FromKnownLess")),
            ];
            entries.push(("cite_fact_id", string(p.cite_fact_id.to_string())));
            if let Some(fact) = runtime.fact_by_id_in_stack(p.cite_fact_id) {
                entries.push(("cite", string(fact.readable_string())));
            }
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::ArcsinPrincipalLowerBound(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessEqualFact")),
                ("rule", string("ArcsinPrincipalLowerBound")),
            ];
            let _ = p;
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::ArcsinPrincipalUpperBound(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessEqualFact")),
                ("rule", string("ArcsinPrincipalUpperBound")),
            ];
            let _ = p;
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::ArccosPrincipalLowerBound(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessEqualFact")),
                ("rule", string("ArccosPrincipalLowerBound")),
            ];
            let _ = p;
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::ArccosPrincipalUpperBound(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessEqualFact")),
                ("rule", string("ArccosPrincipalUpperBound")),
            ];
            let _ = p;
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::UnitCircleLowerBound(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessEqualFact")),
                ("rule", string("UnitCircleLowerBound")),
            ];
            let _ = p;
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::UnitCircleUpperBound(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessEqualFact")),
                ("rule", string("UnitCircleUpperBound")),
            ];
            let _ = p;
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::AbsNonnegative(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessEqualFact")),
                ("rule", string("AbsNonnegative")),
            ];
            let _ = p;
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::AddRightNonnegative(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessEqualFact")),
                ("rule", string("AddRightNonnegative")),
            ];
            entries.push(("nonnegative_addend_proof", project_verify_fact(&p.nonnegative_addend_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::AddLeftNonnegative(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessEqualFact")),
                ("rule", string("AddLeftNonnegative")),
            ];
            entries.push(("nonnegative_addend_proof", project_verify_fact(&p.nonnegative_addend_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::AddRightCongruence(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessEqualFact")),
                ("rule", string("AddRightCongruence")),
            ];
            entries.push(("premise_proof", project_verify_fact(&p.premise_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::AddLeftCongruence(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessEqualFact")),
                ("rule", string("AddLeftCongruence")),
            ];
            entries.push(("premise_proof", project_verify_fact(&p.premise_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::SubNonnegative(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessEqualFact")),
                ("rule", string("SubNonnegative")),
            ];
            entries.push(("nonnegative_subtrahend_proof", project_verify_fact(&p.nonnegative_subtrahend_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::MulLeftNonnegativeMonotone(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessEqualFact")),
                ("rule", string("MulLeftNonnegativeMonotone")),
            ];
            entries.push(("nonnegative_factor_proof", project_verify_fact(&p.nonnegative_factor_proof, runtime)));
            entries.push(("order_premise_proof", project_verify_fact(&p.order_premise_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::MulRightNonnegativeMonotone(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessEqualFact")),
                ("rule", string("MulRightNonnegativeMonotone")),
            ];
            entries.push(("nonnegative_factor_proof", project_verify_fact(&p.nonnegative_factor_proof, runtime)));
            entries.push(("order_premise_proof", project_verify_fact(&p.order_premise_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::AbsLeFromSymmetricBounds(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessEqualFact")),
                ("rule", string("AbsLeFromSymmetricBounds")),
            ];
            entries.push(("upper_proof", project_verify_fact(&p.upper_proof, runtime)));
            entries.push(("neg_upper_proof", project_verify_fact(&p.neg_upper_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::AbsLeImpliesUpper(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessEqualFact")),
                ("rule", string("AbsLeImpliesUpper")),
            ];
            entries.push(("cite_fact_id", string(p.cite_fact_id.to_string())));
            if let Some(fact) = runtime.fact_by_id_in_stack(p.cite_fact_id) {
                entries.push(("cite", string(fact.readable_string())));
            }
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::AbsLeImpliesNegUpper(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessEqualFact")),
                ("rule", string("AbsLeImpliesNegUpper")),
            ];
            entries.push(("cite_fact_id", string(p.cite_fact_id.to_string())));
            if let Some(fact) = runtime.fact_by_id_in_stack(p.cite_fact_id) {
                entries.push(("cite", string(fact.readable_string())));
            }
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::AbsSelfUpper(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessEqualFact")),
                ("rule", string("AbsSelfUpper")),
            ];
            let _ = p;
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::AbsSelfLower(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessEqualFact")),
                ("rule", string("AbsSelfLower")),
            ];
            let _ = p;
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::AbsTriangleInequality(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessEqualFact")),
                ("rule", string("AbsTriangleInequality")),
            ];
            let _ = p;
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::AbsReverseTriangleAdd(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessEqualFact")),
                ("rule", string("AbsReverseTriangleAdd")),
            ];
            let _ = p;
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::AbsReverseTriangleSub(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessEqualFact")),
                ("rule", string("AbsReverseTriangleSub")),
            ];
            let _ = p;
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::SumOfNonnegatives(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessEqualFact")),
                ("rule", string("SumOfNonnegatives")),
            ];
            entries.push(("left_nonnegative_proof", project_verify_fact(&p.left_nonnegative_proof, runtime)));
            entries.push(("right_nonnegative_proof", project_verify_fact(&p.right_nonnegative_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::ProductOfNonnegatives(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessEqualFact")),
                ("rule", string("ProductOfNonnegatives")),
            ];
            entries.push(("left_nonnegative_proof", project_verify_fact(&p.left_nonnegative_proof, runtime)));
            entries.push(("right_nonnegative_proof", project_verify_fact(&p.right_nonnegative_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::EvenPowNonnegative(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessEqualFact")),
                ("rule", string("EvenPowNonnegative")),
            ];
            let _ = p;
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::PowNonnegFromPositiveBase(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessEqualFact")),
                ("rule", string("PowNonnegFromPositiveBase")),
            ];
            entries.push(("base_positive_proof", project_verify_fact(&p.base_positive_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::PowNonnegFromNonnegBasePosIntExp(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessEqualFact")),
                ("rule", string("PowNonnegFromNonnegBasePosIntExp")),
            ];
            entries.push(("base_nonnegative_proof", project_verify_fact(&p.base_nonnegative_proof, runtime)));
            entries.push(("exp_in_positive_natural_proof", project_verify_fact(&p.exp_in_positive_natural_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::SqrtNonnegative(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessEqualFact")),
                ("rule", string("SqrtNonnegative")),
            ];
            entries.push(("arg_nonnegative_proof", project_verify_fact(&p.arg_nonnegative_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::SqrtMonotoneNondecreasing(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessEqualFact")),
                ("rule", string("SqrtMonotoneNondecreasing")),
            ];
            entries.push(("left_nonnegative_proof", project_verify_fact(&p.left_nonnegative_proof, runtime)));
            entries.push(("right_nonnegative_proof", project_verify_fact(&p.right_nonnegative_proof, runtime)));
            entries.push(("args_order_proof", project_verify_fact(&p.args_order_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::FromKnownInPositiveNatural(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessEqualFact")),
                ("rule", string("FromKnownInPositiveNatural")),
            ];
            entries.push(("cite_fact_id", string(p.cite_fact_id.to_string())));
            if let Some(fact) = runtime.fact_by_id_in_stack(p.cite_fact_id) {
                entries.push(("cite", string(fact.readable_string())));
            }
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::LogOrderPreservingWeak(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessEqualFact")),
                ("rule", string("LogOrderPreservingWeak")),
            ];
            entries.push(("base_gt_one_proof", project_verify_fact(&p.base_gt_one_proof, runtime)));
            entries.push(("left_arg_positive_proof", project_verify_fact(&p.left_arg_positive_proof, runtime)));
            entries.push(("right_arg_positive_proof", project_verify_fact(&p.right_arg_positive_proof, runtime)));
            entries.push(("args_order_proof", project_verify_fact(&p.args_order_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::LessEqualTransitivity(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessEqualFact")),
                ("rule", string("LessEqualTransitivity")),
            ];
            entries.push(("cite_fact_id", string(p.left_to_mid_cite_fact_id.to_string())));
            if let Some(fact) = runtime.fact_by_id_in_stack(p.left_to_mid_cite_fact_id) {
                entries.push(("cite", string(fact.readable_string())));
            }
            entries.push(("cite_fact_id", string(p.mid_to_right_cite_fact_id.to_string())));
            if let Some(fact) = runtime.fact_by_id_in_stack(p.mid_to_right_cite_fact_id) {
                entries.push(("cite", string(fact.readable_string())));
            }
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::LessEqualFromNonnegDifference(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessEqualFact")),
                ("rule", string("LessEqualFromNonnegDifference")),
            ];
            entries.push(("cite_fact_id", string(p.cite_fact_id.to_string())));
            if let Some(fact) = runtime.fact_by_id_in_stack(p.cite_fact_id) {
                entries.push(("cite", string(fact.readable_string())));
            }
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::NonnegDifferenceFromLessEqual(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessEqualFact")),
                ("rule", string("NonnegDifferenceFromLessEqual")),
            ];
            entries.push(("cite_fact_id", string(p.cite_fact_id.to_string())));
            if let Some(fact) = runtime.fact_by_id_in_stack(p.cite_fact_id) {
                entries.push(("cite", string(fact.readable_string())));
            }
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::ModRemainderNonnegative(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessEqualFact")),
                ("rule", string("ModRemainderNonnegative")),
            ];
            entries.push(("dividend_in_z_proof", project_verify_fact(&p.dividend_in_z_proof, runtime)));
            entries.push(("modulus_in_n_pos_proof", project_verify_fact(&p.modulus_in_n_pos_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::DivMonotoneWeakSamePosDivisor(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessEqualFact")),
                ("rule", string("DivMonotoneWeakSamePosDivisor")),
            ];
            entries.push(("divisor_pos_proof", project_verify_fact(&p.divisor_pos_proof, runtime)));
            entries.push(("numerators_order_proof", project_verify_fact(&p.numerators_order_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::FiniteSetSizeNonnegativeLe(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessEqualFact")),
                ("rule", string("FiniteSetSizeNonnegativeLe")),
            ];
            entries.push(("finite_proof", project_verify_fact(&p.finite_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::FiniteSetSizeAtLeastOneLe(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessEqualFact")),
                ("rule", string("FiniteSetSizeAtLeastOneLe")),
            ];
            entries.push(("finite_proof", project_verify_fact(&p.finite_proof, runtime)));
            entries.push(("nonempty_proof", project_verify_fact(&p.nonempty_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::FiniteSetSizeSubsetLe(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessEqualFact")),
                ("rule", string("FiniteSetSizeSubsetLe")),
            ];
            entries.push(("left_finite_proof", project_verify_fact(&p.left_finite_proof, runtime)));
            entries.push(("right_finite_proof", project_verify_fact(&p.right_finite_proof, runtime)));
            entries.push(("subset_proof", project_verify_fact(&p.subset_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::DivMonotoneWeakSameNegDivisor(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessEqualFact")),
                ("rule", string("DivMonotoneWeakSameNegDivisor")),
            ];
            entries.push(("divisor_neg_proof", project_verify_fact(&p.divisor_neg_proof, runtime)));
            entries.push(("numerators_order_proof", project_verify_fact(&p.numerators_order_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::LessEqualFromPosDivProductBound(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessEqualFact")),
                ("rule", string("LessEqualFromPosDivProductBound")),
            ];
            entries.push(("divisor_pos_proof", project_verify_fact(&p.divisor_pos_proof, runtime)));
            entries.push(("product_bound_proof", project_verify_fact(&p.product_bound_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::LessEqualFromPosDenomQuotientBound(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessEqualFact")),
                ("rule", string("LessEqualFromPosDenomQuotientBound")),
            ];
            entries.push(("divisor_pos_proof", project_verify_fact(&p.divisor_pos_proof, runtime)));
            entries.push(("quotient_bound_proof", project_verify_fact(&p.quotient_bound_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::NumericLowerBoundWeakenLe(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessEqualFact")),
                ("rule", string("NumericLowerBoundWeakenLe")),
            ];
            entries.push(("cite_fact_id", string(p.cite_fact_id.to_string())));
            if let Some(fact) = runtime.fact_by_id_in_stack(p.cite_fact_id) {
                entries.push(("cite", string(fact.readable_string())));
            }
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::NumericLowerBoundFromStrictPredecessorLe(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessEqualFact")),
                ("rule", string("NumericLowerBoundFromStrictPredecessorLe")),
            ];
            entries.push(("cite_fact_id", string(p.cite_fact_id.to_string())));
            if let Some(fact) = runtime.fact_by_id_in_stack(p.cite_fact_id) {
                entries.push(("cite", string(fact.readable_string())));
            }
            entries.push(("in_z_proof", project_verify_fact(&p.in_z_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::NumericUpperBoundWeakenLe(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessEqualFact")),
                ("rule", string("NumericUpperBoundWeakenLe")),
            ];
            entries.push(("cite_fact_id", string(p.cite_fact_id.to_string())));
            if let Some(fact) = runtime.fact_by_id_in_stack(p.cite_fact_id) {
                entries.push(("cite", string(fact.readable_string())));
            }
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::IntegerSuccessorLe(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessEqualFact")),
                ("rule", string("IntegerSuccessorLe")),
            ];
            entries.push(("left_in_z_proof", project_verify_fact(&p.left_in_z_proof, runtime)));
            entries.push(("right_in_z_proof", project_verify_fact(&p.right_in_z_proof, runtime)));
            entries.push(("strict_proof", project_verify_fact(&p.strict_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::IntegerAdjacencyLe(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessEqualFact")),
                ("rule", string("IntegerAdjacencyLe")),
            ];
            entries.push(("left_in_z_proof", project_verify_fact(&p.left_in_z_proof, runtime)));
            entries.push(("right_in_z_proof", project_verify_fact(&p.right_in_z_proof, runtime)));
            entries.push(("strict_proof", project_verify_fact(&p.strict_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::IntegerPredecessorLe(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessEqualFact")),
                ("rule", string("IntegerPredecessorLe")),
            ];
            entries.push(("left_in_z_proof", project_verify_fact(&p.left_in_z_proof, runtime)));
            entries.push(("right_in_z_proof", project_verify_fact(&p.right_in_z_proof, runtime)));
            entries.push(("strict_proof", project_verify_fact(&p.strict_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::IntegerDiffAtLeastOneLe(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessEqualFact")),
                ("rule", string("IntegerDiffAtLeastOneLe")),
            ];
            entries.push(("left_in_z_proof", project_verify_fact(&p.left_in_z_proof, runtime)));
            entries.push(("right_in_z_proof", project_verify_fact(&p.right_in_z_proof, runtime)));
            entries.push(("strict_proof", project_verify_fact(&p.strict_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::FiniteSetMaxMemberLe(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessEqualFact")),
                ("rule", string("FiniteSetMaxMemberLe")),
            ];
            entries.push(("member_proof", project_verify_fact(&p.member_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::FiniteSetMinMemberLe(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessEqualFact")),
                ("rule", string("FiniteSetMinMemberLe")),
            ];
            entries.push(("member_proof", project_verify_fact(&p.member_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::FiniteSetSizeUnionLeSum(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessEqualFact")),
                ("rule", string("FiniteSetSizeUnionLeSum")),
            ];
            entries.push(("left_finite_proof", project_verify_fact(&p.left_finite_proof, runtime)));
            entries.push(("right_finite_proof", project_verify_fact(&p.right_finite_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::FiniteSetSizeSurjectionCodomainLeDomain(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessEqualFact")),
                ("rule", string("FiniteSetSizeSurjectionCodomainLeDomain")),
            ];
            entries.push(("cite_fact_id", string(p.cite_surjection_fact_id.to_string())));
            if let Some(fact) = runtime.fact_by_id_in_stack(p.cite_surjection_fact_id) {
                entries.push(("cite", string(fact.readable_string())));
            }
            entries.push(("domain_finite_proof", project_verify_fact(&p.domain_finite_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::OrderFlipMulMinusOne(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessEqualFact")),
                ("rule", string("OrderFlipMulMinusOne")),
            ];
            entries.push(("cite_fact_id", string(p.cite_fact_id.to_string())));
            if let Some(fact) = runtime.fact_by_id_in_stack(p.cite_fact_id) {
                entries.push(("cite", string(fact.readable_string())));
            }
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::OrderSignFromNegativeLiteralBound(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessEqualFact")),
                ("rule", string("OrderSignFromNegativeLiteralBound")),
            ];
            entries.push(("cite_fact_id", string(p.cite_fact_id.to_string())));
            if let Some(fact) = runtime.fact_by_id_in_stack(p.cite_fact_id) {
                entries.push(("cite", string(fact.readable_string())));
            }
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterEqualFact(br::greater_equal::GreaterEqualFactSearchProofByBuiltinRule::ClosedNumericComparison(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("GreaterEqualFact")),
                ("rule", string("ClosedNumericComparison")),
            ];
            entries.push(("left_normal", string(p.left_normal.clone())));
            entries.push(("right_normal", string(p.right_normal.clone())));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterEqualFact(br::greater_equal::GreaterEqualFactSearchProofByBuiltinRule::OrderReflexivity(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("GreaterEqualFact")),
                ("rule", string("OrderReflexivity")),
            ];
            entries.push(("repeated_object", string(p.repeated_object.readable_string())));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterEqualFact(br::greater_equal::GreaterEqualFactSearchProofByBuiltinRule::FromKnownGreater(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("GreaterEqualFact")),
                ("rule", string("FromKnownGreater")),
            ];
            entries.push(("cite_fact_id", string(p.cite_fact_id.to_string())));
            if let Some(fact) = runtime.fact_by_id_in_stack(p.cite_fact_id) {
                entries.push(("cite", string(fact.readable_string())));
            }
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterEqualFact(br::greater_equal::GreaterEqualFactSearchProofByBuiltinRule::FromKnownInPositiveNatural(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("GreaterEqualFact")),
                ("rule", string("FromKnownInPositiveNatural")),
            ];
            entries.push(("cite_fact_id", string(p.cite_fact_id.to_string())));
            if let Some(fact) = runtime.fact_by_id_in_stack(p.cite_fact_id) {
                entries.push(("cite", string(fact.readable_string())));
            }
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterEqualFact(br::greater_equal::GreaterEqualFactSearchProofByBuiltinRule::PredecessorNonNegFromAtLeastOne(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("GreaterEqualFact")),
                ("rule", string("PredecessorNonNegFromAtLeastOne")),
            ];
            entries.push(("cite_fact_id", string(p.cite_at_least_one_fact_id.to_string())));
            if let Some(fact) = runtime.fact_by_id_in_stack(p.cite_at_least_one_fact_id) {
                entries.push(("cite", string(fact.readable_string())));
            }
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterEqualFact(br::greater_equal::GreaterEqualFactSearchProofByBuiltinRule::FiniteSetSizeNonnegative(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("GreaterEqualFact")),
                ("rule", string("FiniteSetSizeNonnegative")),
            ];
            entries.push(("finite_proof", project_verify_fact(&p.finite_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterEqualFact(br::greater_equal::GreaterEqualFactSearchProofByBuiltinRule::FiniteSetSizeAtLeastOne(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("GreaterEqualFact")),
                ("rule", string("FiniteSetSizeAtLeastOne")),
            ];
            entries.push(("finite_proof", project_verify_fact(&p.finite_proof, runtime)));
            entries.push(("nonempty_proof", project_verify_fact(&p.nonempty_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterEqualFact(br::greater_equal::GreaterEqualFactSearchProofByBuiltinRule::OrderFlipMulMinusOne(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("GreaterEqualFact")),
                ("rule", string("OrderFlipMulMinusOne")),
            ];
            entries.push(("cite_fact_id", string(p.cite_fact_id.to_string())));
            if let Some(fact) = runtime.fact_by_id_in_stack(p.cite_fact_id) {
                entries.push(("cite", string(fact.readable_string())));
            }
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::IsSetFact(br::is_set::IsSetFactSearchProofByBuiltinRule::AlwaysTrue(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("IsSetFact")),
                ("rule", string("AlwaysTrue")),
            ];
            let _ = p;
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::IsNonemptySetFact(br::is_nonempty_set::IsNonemptySetFactSearchProofByBuiltinRule::StandardSetNonempty(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("IsNonemptySetFact")),
                ("rule", string("StandardSetNonempty")),
            ];
            entries.push(("target_set", string(p.target_set.ir().as_str().to_string())));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::IsNonemptySetFact(br::is_nonempty_set::IsNonemptySetFactSearchProofByBuiltinRule::LiteralListSetNonempty(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("IsNonemptySetFact")),
                ("rule", string("LiteralListSetNonempty")),
            ];
            let _ = p;
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::IsNonemptySetFact(br::is_nonempty_set::IsNonemptySetFactSearchProofByBuiltinRule::PowerSetNonempty(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("IsNonemptySetFact")),
                ("rule", string("PowerSetNonempty")),
            ];
            let _ = p;
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::IsNonemptySetFact(br::is_nonempty_set::IsNonemptySetFactSearchProofByBuiltinRule::OneSideInfinityIntervalNonempty(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("IsNonemptySetFact")),
                ("rule", string("OneSideInfinityIntervalNonempty")),
            ];
            let _ = p;
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::IsFiniteSetFact(br::is_finite_set::IsFiniteSetFactSearchProofByBuiltinRule::ListSet(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("IsFiniteSetFact")),
                ("rule", string("ListSet")),
            ];
            let _ = p;
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::IsFiniteSetFact(br::is_finite_set::IsFiniteSetFactSearchProofByBuiltinRule::ClosedRange(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("IsFiniteSetFact")),
                ("rule", string("ClosedRange")),
            ];
            let _ = p;
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::IsFiniteSetFact(br::is_finite_set::IsFiniteSetFactSearchProofByBuiltinRule::Range(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("IsFiniteSetFact")),
                ("rule", string("Range")),
            ];
            let _ = p;
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::IsFiniteSetFact(br::is_finite_set::IsFiniteSetFactSearchProofByBuiltinRule::FiniteSeqZeroLength(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("IsFiniteSetFact")),
                ("rule", string("FiniteSeqZeroLength")),
            ];
            let _ = p;
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::IsFiniteSetFact(br::is_finite_set::IsFiniteSetFactSearchProofByBuiltinRule::FiniteSeqFromFiniteCodomain(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("IsFiniteSetFact")),
                ("rule", string("FiniteSeqFromFiniteCodomain")),
            ];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(br::in_fact::InFactSearchProofByBuiltinRule::ClosedNumericMembership(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("InFact")),
                ("rule", string("ClosedNumericMembership")),
            ];
            let _ = p;
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(br::in_fact::InFactSearchProofByBuiltinRule::ComplexArithmeticClosure(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("InFact")),
                ("rule", string("ComplexArithmeticClosure")),
            ];
            let _ = p;
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(br::in_fact::InFactSearchProofByBuiltinRule::RealTrigClosure(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("InFact")),
                ("rule", string("RealTrigClosure")),
            ];
            let _ = p;
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(br::in_fact::InFactSearchProofByBuiltinRule::RealTrigInComplex(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("InFact")),
                ("rule", string("RealTrigInComplex")),
            ];
            let _ = p;
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(br::in_fact::InFactSearchProofByBuiltinRule::ComplexCoordinateInReal(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("InFact")),
                ("rule", string("ComplexCoordinateInReal")),
            ];
            let _ = p;
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(br::in_fact::InFactSearchProofByBuiltinRule::ComplexCoordinateInComplex(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("InFact")),
                ("rule", string("ComplexCoordinateInComplex")),
            ];
            let _ = p;
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(br::in_fact::InFactSearchProofByBuiltinRule::RealArithmeticClosure(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("InFact")),
                ("rule", string("RealArithmeticClosure")),
            ];
            let _ = p;
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(br::in_fact::InFactSearchProofByBuiltinRule::NativeScalarCodomain(p)) => {
            object_for(runtime, vec![
                ("type", string("builtin_rule")),
                ("family", string("InFact")),
                ("rule", string("NativeScalarCodomain")),
                ("codomain", string(p.codomain.ir().as_str().to_string())),
            ])
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(br::in_fact::InFactSearchProofByBuiltinRule::StandardSetSubsetMembership(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("InFact")),
                ("rule", string("StandardSetSubsetMembership")),
            ];
            entries.push(("source_set", string(p.source_set.ir().as_str().to_string())));
            let _ = (&p.source_membership_proof, runtime);
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(br::in_fact::InFactSearchProofByBuiltinRule::SetBuilderMembership(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("InFact")),
                ("rule", string("SetBuilderMembership")),
            ];
            let _ = &p.requirement_facts;
            entries.push(("requirement_facts", string("<Vec<Fact>>")));
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(br::in_fact::InFactSearchProofByBuiltinRule::NativeConstantMembership(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("InFact")),
                ("rule", string("NativeConstantMembership")),
            ];
            let _ = &p.kind;
            entries.push(("kind", string("<NativeConstantMembershipKind>")));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(br::in_fact::InFactSearchProofByBuiltinRule::ListSetElementMembership(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("InFact")),
                ("rule", string("ListSetElementMembership")),
            ];
            entries.push(("selected_index", JsonValue::Number(p.selected_index as f64)));
            entries.push(("equality_proof", project_verify_fact(&p.equality_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(br::in_fact::InFactSearchProofByBuiltinRule::CartMembership(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("InFact")),
                ("rule", string("CartMembership")),
            ];
            let _ = &p.shape_and_dimension;
            entries.push(("shape_and_dimension", string("<Option<CartMembershipShapeProof>>")));
            entries.push(("coordinate_memberships", project_verify_facts(&p.coordinate_memberships, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(br::in_fact::InFactSearchProofByBuiltinRule::PowerSetMembership(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("InFact")),
                ("rule", string("PowerSetMembership")),
            ];
            entries.push(("subset_proof", project_verify_fact(&p.subset_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(br::in_fact::InFactSearchProofByBuiltinRule::StructObjMembership(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("InFact")),
                ("rule", string("StructObjMembership")),
            ];
            entries.push(("carrier_obligations", project_verify_facts(&p.carrier_obligations, runtime)));
            entries.push(("equivalent_fact_proofs", project_verify_facts(&p.equivalent_fact_proofs, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(br::in_fact::InFactSearchProofByBuiltinRule::PredecessorInNatural(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("InFact")),
                ("rule", string("PredecessorInNatural")),
            ];
            entries.push(("cite_fact_id", string(p.cite_in_n_fact_id.to_string())));
            if let Some(fact) = runtime.fact_by_id_in_stack(p.cite_in_n_fact_id) {
                entries.push(("cite", string(fact.readable_string())));
            }
            entries.push(("cite_fact_id", string(p.cite_at_least_one_fact_id.to_string())));
            if let Some(fact) = runtime.fact_by_id_in_stack(p.cite_at_least_one_fact_id) {
                entries.push(("cite", string(fact.readable_string())));
            }
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(br::in_fact::InFactSearchProofByBuiltinRule::FnApplicationInCodomain(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("InFact")),
                ("rule", string("FnApplicationInCodomain")),
            ];
            entries.push(("cite_fact_id", string(p.cite_in_function_set_fact_id.to_string())));
            if let Some(fact) = runtime.fact_by_id_in_stack(p.cite_in_function_set_fact_id) {
                entries.push(("cite", string(fact.readable_string())));
            }
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(br::in_fact::InFactSearchProofByBuiltinRule::FnApplicationInFnRange(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("InFact")),
                ("rule", string("FnApplicationInFnRange")),
            ];
            let _ = p;
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(br::in_fact::InFactSearchProofByBuiltinRule::UnionMembershipFromLeft(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("InFact")),
                ("rule", string("UnionMembershipFromLeft")),
            ];
            entries.push(("left_membership_proof", project_verify_fact(&p.left_membership_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(br::in_fact::InFactSearchProofByBuiltinRule::UnionMembershipFromRight(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("InFact")),
                ("rule", string("UnionMembershipFromRight")),
            ];
            entries.push(("right_membership_proof", project_verify_fact(&p.right_membership_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(br::in_fact::InFactSearchProofByBuiltinRule::IntersectMembership(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("InFact")),
                ("rule", string("IntersectMembership")),
            ];
            entries.push(("left_membership_proof", project_verify_fact(&p.left_membership_proof, runtime)));
            entries.push(("right_membership_proof", project_verify_fact(&p.right_membership_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(br::in_fact::InFactSearchProofByBuiltinRule::SetMinusMembership(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("InFact")),
                ("rule", string("SetMinusMembership")),
            ];
            entries.push(("left_membership_proof", project_verify_fact(&p.left_membership_proof, runtime)));
            entries.push(("right_non_membership_proof", project_verify_fact(&p.right_non_membership_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(br::in_fact::InFactSearchProofByBuiltinRule::FamilyUnionMembershipFromMember(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("InFact")),
                ("rule", string("FamilyUnionMembershipFromMember")),
            ];
            entries.push(("cite_fact_id", string(p.cite_member_set_in_family_fact_id.to_string())));
            if let Some(fact) = runtime.fact_by_id_in_stack(p.cite_member_set_in_family_fact_id) {
                entries.push(("cite", string(fact.readable_string())));
            }
            entries.push(("element_in_member_set_proof", project_verify_fact(&p.element_in_member_set_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(br::in_fact::InFactSearchProofByBuiltinRule::IndexUnionMembershipFromIndex(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("InFact")),
                ("rule", string("IndexUnionMembershipFromIndex")),
            ];
            entries.push(("cite_fact_id", string(p.cite_index_in_index_set_fact_id.to_string())));
            if let Some(fact) = runtime.fact_by_id_in_stack(p.cite_index_in_index_set_fact_id) {
                entries.push(("cite", string(fact.readable_string())));
            }
            entries.push(("element_in_fiber_proof", project_verify_fact(&p.element_in_fiber_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(br::in_fact::InFactSearchProofByBuiltinRule::IntervalMembership(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("InFact")),
                ("rule", string("IntervalMembership")),
            ];
            entries.push(("in_real_proof", project_verify_fact(&p.in_real_proof, runtime)));
            entries.push(("lower_bound_proof", project_verify_fact(&p.lower_bound_proof, runtime)));
            entries.push(("upper_bound_proof", project_verify_fact(&p.upper_bound_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(br::in_fact::InFactSearchProofByBuiltinRule::OneSideInfinityIntervalMembership(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("InFact")),
                ("rule", string("OneSideInfinityIntervalMembership")),
            ];
            entries.push(("in_real_proof", project_verify_fact(&p.in_real_proof, runtime)));
            entries.push(("endpoint_bound_proof", project_verify_fact(&p.endpoint_bound_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(br::in_fact::InFactSearchProofByBuiltinRule::AddInNatural(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("InFact")),
                ("rule", string("AddInNatural")),
            ];
            entries.push(("left_in_n_proof", project_verify_fact(&p.left_in_n_proof, runtime)));
            entries.push(("right_in_n_proof", project_verify_fact(&p.right_in_n_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(br::in_fact::InFactSearchProofByBuiltinRule::MulInNatural(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("InFact")),
                ("rule", string("MulInNatural")),
            ];
            entries.push(("left_in_n_proof", project_verify_fact(&p.left_in_n_proof, runtime)));
            entries.push(("right_in_n_proof", project_verify_fact(&p.right_in_n_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::IsCartFact(br::is_cart::IsCartFactSearchProofByBuiltinRule::CartConstructor(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("IsCartFact")),
                ("rule", string("CartConstructor")),
            ];
            let _ = p;
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::IsTupleFact(br::is_tuple::IsTupleFactSearchProofByBuiltinRule::TupleLiteral(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("IsTupleFact")),
                ("rule", string("TupleLiteral")),
            ];
            let _ = p;
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::SubsetFact(br::subset::SubsetFactSearchProofByBuiltinRule::StandardSetSubset(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("SubsetFact")),
                ("rule", string("StandardSetSubset")),
            ];
            entries.push(("left", string(p.left.ir().as_str().to_string())));
            entries.push(("right", string(p.right.ir().as_str().to_string())));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::SubsetFact(br::subset::SubsetFactSearchProofByBuiltinRule::IntersectSubsetLeft(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("SubsetFact")),
                ("rule", string("IntersectSubsetLeft")),
            ];
            let _ = p;
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::SubsetFact(br::subset::SubsetFactSearchProofByBuiltinRule::IntersectSubsetRight(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("SubsetFact")),
                ("rule", string("IntersectSubsetRight")),
            ];
            let _ = p;
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::SubsetFact(br::subset::SubsetFactSearchProofByBuiltinRule::SubsetUnionLeft(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("SubsetFact")),
                ("rule", string("SubsetUnionLeft")),
            ];
            let _ = p;
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::SubsetFact(br::subset::SubsetFactSearchProofByBuiltinRule::SubsetUnionRight(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("SubsetFact")),
                ("rule", string("SubsetUnionRight")),
            ];
            let _ = p;
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::SubsetFact(br::subset::SubsetFactSearchProofByBuiltinRule::SetMinusSubsetLeft(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("SubsetFact")),
                ("rule", string("SetMinusSubsetLeft")),
            ];
            let _ = p;
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::SubsetFact(br::subset::SubsetFactSearchProofByBuiltinRule::RealIntervalSubsetReal(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("SubsetFact")),
                ("rule", string("RealIntervalSubsetReal")),
            ];
            let _ = p;
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::SubsetFact(br::subset::SubsetFactSearchProofByBuiltinRule::SetBuilderSubsetOfParamSet(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("SubsetFact")),
                ("rule", string("SetBuilderSubsetOfParamSet")),
            ];
            let _ = p;
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::SubsetFact(br::subset::SubsetFactSearchProofByBuiltinRule::SubsetReflexivity(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("SubsetFact")),
                ("rule", string("SubsetReflexivity")),
            ];
            let _ = p;
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::SubsetFact(br::subset::SubsetFactSearchProofByBuiltinRule::UnionSubsetFromBothOperands(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("SubsetFact")),
                ("rule", string("UnionSubsetFromBothOperands")),
            ];
            entries.push(("left_operand_subset_proof", project_verify_fact(&p.left_operand_subset_proof, runtime)));
            entries.push(("right_operand_subset_proof", project_verify_fact(&p.right_operand_subset_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::SubsetFact(br::subset::SubsetFactSearchProofByBuiltinRule::IntersectSubsetFromLeftUpperBound(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("SubsetFact")),
                ("rule", string("IntersectSubsetFromLeftUpperBound")),
            ];
            entries.push(("left_operand_subset_proof", project_verify_fact(&p.left_operand_subset_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::SubsetFact(br::subset::SubsetFactSearchProofByBuiltinRule::IntersectSubsetFromRightUpperBound(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("SubsetFact")),
                ("rule", string("IntersectSubsetFromRightUpperBound")),
            ];
            entries.push(("right_operand_subset_proof", project_verify_fact(&p.right_operand_subset_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::SubsetFact(br::subset::SubsetFactSearchProofByBuiltinRule::ListSetSubsetFromMembers(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("SubsetFact")),
                ("rule", string("ListSetSubsetFromMembers")),
            ];
            entries.push(("member_in_proofs", project_verify_facts(&p.member_in_proofs, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::SubsetFact(br::subset::SubsetFactSearchProofByBuiltinRule::UnionSubsetFromComponentwise(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("SubsetFact")),
                ("rule", string("UnionSubsetFromComponentwise")),
            ];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::SubsetFact(br::subset::SubsetFactSearchProofByBuiltinRule::IntegerRangeSubsetNumericCarrier(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("SubsetFact")),
                ("rule", string("IntegerRangeSubsetNumericCarrier")),
            ];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::SubsetFact(br::subset::SubsetFactSearchProofByBuiltinRule::SubsetPowerSetMonotone(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("SubsetFact")),
                ("rule", string("SubsetPowerSetMonotone")),
            ];
            entries.push(("base_subset_proof", project_verify_fact(&p.base_subset_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::SubsetFact(br::subset::SubsetFactSearchProofByBuiltinRule::SubsetSetMinusCommonRightMonotone(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("SubsetFact")),
                ("rule", string("SubsetSetMinusCommonRightMonotone")),
            ];
            entries.push(("left_operand_subset_proof", project_verify_fact(&p.left_operand_subset_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::SubsetFact(br::subset::SubsetFactSearchProofByBuiltinRule::SubsetCartComponentwise(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("SubsetFact")),
                ("rule", string("SubsetCartComponentwise")),
            ];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::SubsetFact(br::subset::SubsetFactSearchProofByBuiltinRule::SubsetTransitivity(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("SubsetFact")),
                ("rule", string("SubsetTransitivity")),
            ];
            entries.push(("left_to_middle_proof", project_verify_fact(&p.left_to_middle_proof, runtime)));
            entries.push(("middle_to_right_proof", project_verify_fact(&p.middle_to_right_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::SupersetFact(br::superset::SupersetFactSearchProofByBuiltinRule::StandardSetSuperset(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("SupersetFact")),
                ("rule", string("StandardSetSuperset")),
            ];
            entries.push(("left", string(p.left.ir().as_str().to_string())));
            entries.push(("right", string(p.right.ir().as_str().to_string())));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::SupersetFact(br::superset::SupersetFactSearchProofByBuiltinRule::SupersetReflexivity(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("SupersetFact")),
                ("rule", string("SupersetReflexivity")),
            ];
            let _ = p;
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotPrimeFact(NotPrimeFactSearchProofByBuiltinRule::NotPrimeByComputation(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("NotPrimeFact")),
                ("rule", string("NotPrimeByComputation")),
            ];
            entries.push(("resolved_value", string(p.resolved_value.clone())));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotCoprimeFact(NotCoprimeFactSearchProofByBuiltinRule::NotCoprimeByComputation(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("NotCoprimeFact")),
                ("rule", string("NotCoprimeByComputation")),
            ];
            entries.push(("left_resolved", string(p.left_resolved.clone())));
            entries.push(("right_resolved", string(p.right_resolved.clone())));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotEqualFact(br::not_equal::NotEqualFactSearchProofByBuiltinRule::ClosedDecimal(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("NotEqualFact")),
                ("rule", string("ClosedDecimal")),
            ];
            entries.push(("left_normal", string(p.left_normal.clone())));
            entries.push(("right_normal", string(p.right_normal.clone())));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotEqualFact(br::not_equal::NotEqualFactSearchProofByBuiltinRule::NotEqualSymmetry(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("NotEqualFact")),
                ("rule", string("NotEqualSymmetry")),
            ];
            entries.push(("alternate_fact", string(p.alternate_fact.readable_string())));
            entries.push(("proof_of_alternate_fact", project_verify_fact(&p.proof_of_alternate_fact, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotEqualFact(br::not_equal::NotEqualFactSearchProofByBuiltinRule::ListSetDifferentLength(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("NotEqualFact")),
                ("rule", string("ListSetDifferentLength")),
            ];
            let _ = p;
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotEqualFact(br::not_equal::NotEqualFactSearchProofByBuiltinRule::FromKnownStrictOrder(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("NotEqualFact")),
                ("rule", string("FromKnownStrictOrder")),
            ];
            entries.push(("cite_fact_id", string(p.cite_fact_id.to_string())));
            if let Some(fact) = runtime.fact_by_id_in_stack(p.cite_fact_id) {
                entries.push(("cite", string(fact.readable_string())));
            }
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotEqualFact(br::not_equal::NotEqualFactSearchProofByBuiltinRule::CosNonzeroOnOpenHalfPi(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("NotEqualFact")),
                ("rule", string("CosNonzeroOnOpenHalfPi")),
            ];
            let _ = p;
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotEqualFact(br::not_equal::NotEqualFactSearchProofByBuiltinRule::CosNonzeroAtZero(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("NotEqualFact")),
                ("rule", string("CosNonzeroAtZero")),
            ];
            let _ = p;
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotEqualFact(br::not_equal::NotEqualFactSearchProofByBuiltinRule::SinNonzeroOnOpenPi(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("NotEqualFact")),
                ("rule", string("SinNonzeroOnOpenPi")),
            ];
            let _ = p;
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotEqualFact(br::not_equal::NotEqualFactSearchProofByBuiltinRule::SinNonzeroAtHalfPi(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("NotEqualFact")),
                ("rule", string("SinNonzeroAtHalfPi")),
            ];
            let _ = p;
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotEqualFact(br::not_equal::NotEqualFactSearchProofByBuiltinRule::AbsNonzeroFromArg(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("NotEqualFact")),
                ("rule", string("AbsNonzeroFromArg")),
            ];
            entries.push(("arg_nonzero_proof", project_verify_fact(&p.arg_nonzero_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotEqualFact(br::not_equal::NotEqualFactSearchProofByBuiltinRule::DiffNonzeroFromInequality(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("NotEqualFact")),
                ("rule", string("DiffNonzeroFromInequality")),
            ];
            entries.push(("operands_unequal_proof", project_verify_fact(&p.operands_unequal_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotEqualFact(br::not_equal::NotEqualFactSearchProofByBuiltinRule::EmptySetFromNonempty(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("NotEqualFact")),
                ("rule", string("EmptySetFromNonempty")),
            ];
            entries.push(("nonempty_proof", project_verify_fact(&p.nonempty_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotEqualFact(br::not_equal::NotEqualFactSearchProofByBuiltinRule::ZeroFromNatAndOneLe(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("NotEqualFact")),
                ("rule", string("ZeroFromNatAndOneLe")),
            ];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotEqualFact(br::not_equal::NotEqualFactSearchProofByBuiltinRule::PowNonzeroFromBase(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("NotEqualFact")),
                ("rule", string("PowNonzeroFromBase")),
            ];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotEqualFact(br::not_equal::NotEqualFactSearchProofByBuiltinRule::DivNonzeroFromFactors(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("NotEqualFact")),
                ("rule", string("DivNonzeroFromFactors")),
            ];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotEqualFact(br::not_equal::NotEqualFactSearchProofByBuiltinRule::ProductComponentNonzero(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("NotEqualFact")),
                ("rule", string("ProductComponentNonzero")),
            ];
            let _ = p;
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotEqualFact(br::not_equal::NotEqualFactSearchProofByBuiltinRule::SqrtNonzeroFromPositiveArg(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("NotEqualFact")),
                ("rule", string("SqrtNonzeroFromPositiveArg")),
            ];
            entries.push(("arg_positive_proof", project_verify_fact(&p.arg_positive_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotEqualFact(br::not_equal::NotEqualFactSearchProofByBuiltinRule::SquareSumNonzeroFromComponent(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("NotEqualFact")),
                ("rule", string("SquareSumNonzeroFromComponent")),
            ];
            entries.push(("component_nonzero_proof", project_verify_fact(&p.component_nonzero_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotEqualFact(br::not_equal::NotEqualFactSearchProofByBuiltinRule::AddNonzeroFromNotEqualNegation(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("NotEqualFact")),
                ("rule", string("AddNonzeroFromNotEqualNegation")),
            ];
            entries.push(("not_equal_negation_proof", project_verify_fact(&p.not_equal_negation_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotEqualFact(br::not_equal::NotEqualFactSearchProofByBuiltinRule::MembershipContradiction(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("NotEqualFact")),
                ("rule", string("MembershipContradiction")),
            ];
            entries.push(("in_proof", project_verify_fact(&p.in_proof, runtime)));
            entries.push(("not_in_proof", project_verify_fact(&p.not_in_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotLessFact(br::not_less::NotLessFactSearchProofByBuiltinRule::ClosedNumericComparison(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("NotLessFact")),
                ("rule", string("ClosedNumericComparison")),
            ];
            entries.push(("left_normal", string(p.left_normal.clone())));
            entries.push(("right_normal", string(p.right_normal.clone())));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotLessFact(br::not_less::NotLessFactSearchProofByBuiltinRule::FromKnownGreater(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("NotLessFact")),
                ("rule", string("FromKnownGreater")),
            ];
            entries.push(("cite_fact_id", string(p.cite_fact_id.to_string())));
            if let Some(fact) = runtime.fact_by_id_in_stack(p.cite_fact_id) {
                entries.push(("cite", string(fact.readable_string())));
            }
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotGreaterFact(br::not_greater::NotGreaterFactSearchProofByBuiltinRule::ClosedNumericComparison(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("NotGreaterFact")),
                ("rule", string("ClosedNumericComparison")),
            ];
            entries.push(("left_normal", string(p.left_normal.clone())));
            entries.push(("right_normal", string(p.right_normal.clone())));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotGreaterFact(br::not_greater::NotGreaterFactSearchProofByBuiltinRule::FromKnownLess(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("NotGreaterFact")),
                ("rule", string("FromKnownLess")),
            ];
            entries.push(("cite_fact_id", string(p.cite_fact_id.to_string())));
            if let Some(fact) = runtime.fact_by_id_in_stack(p.cite_fact_id) {
                entries.push(("cite", string(fact.readable_string())));
            }
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotLessEqualFact(br::not_less_equal::NotLessEqualFactSearchProofByBuiltinRule::ClosedNumericComparison(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("NotLessEqualFact")),
                ("rule", string("ClosedNumericComparison")),
            ];
            entries.push(("left_normal", string(p.left_normal.clone())));
            entries.push(("right_normal", string(p.right_normal.clone())));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotGreaterEqualFact(br::not_greater_equal::NotGreaterEqualFactSearchProofByBuiltinRule::ClosedNumericComparison(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("NotGreaterEqualFact")),
                ("rule", string("ClosedNumericComparison")),
            ];
            entries.push(("left_normal", string(p.left_normal.clone())));
            entries.push(("right_normal", string(p.right_normal.clone())));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotIsSetFact(_) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("family", string("NotIsSetFact")),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotIsNonemptySetFact(br::not_is_nonempty_set::NotIsNonemptySetFactSearchProofByBuiltinRule::EmptyListSet(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("NotIsNonemptySetFact")),
                ("rule", string("EmptyListSet")),
            ];
            let _ = p;
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotIsFiniteSetFact(br::not_is_finite_set::NotIsFiniteSetFactSearchProofByBuiltinRule::StandardInfiniteSet(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("NotIsFiniteSetFact")),
                ("rule", string("StandardInfiniteSet")),
            ];
            let _ = p;
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotIsFiniteSetFact(br::not_is_finite_set::NotIsFiniteSetFactSearchProofByBuiltinRule::SetMinusInfiniteOfInfiniteFinite(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("NotIsFiniteSetFact")),
                ("rule", string("SetMinusInfiniteOfInfiniteFinite")),
            ];
            entries.push(("left_infinite_proof", project_verify_fact(&p.left_infinite_proof, runtime)));
            entries.push(("right_finite_proof", project_verify_fact(&p.right_finite_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotInFact(br::not_in_fact::NotInFactSearchProofByBuiltinRule::ClosedNumericNonMembership(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("NotInFact")),
                ("rule", string("ClosedNumericNonMembership")),
            ];
            entries.push(("normal", string(p.normal.clone())));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotInFact(br::not_in_fact::NotInFactSearchProofByBuiltinRule::ListSetExhaustiveDisequality(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("NotInFact")),
                ("rule", string("ListSetExhaustiveDisequality")),
            ];
            entries.push(("disequality_proofs", project_verify_facts(&p.disequality_proofs, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotInFact(br::not_in_fact::NotInFactSearchProofByBuiltinRule::NonMembershipOfIntersectFromLeft(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("NotInFact")),
                ("rule", string("NonMembershipOfIntersectFromLeft")),
            ];
            entries.push(("left_non_membership_proof", project_verify_fact(&p.left_non_membership_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotInFact(br::not_in_fact::NotInFactSearchProofByBuiltinRule::NonMembershipOfIntersectFromRight(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("NotInFact")),
                ("rule", string("NonMembershipOfIntersectFromRight")),
            ];
            entries.push(("right_non_membership_proof", project_verify_fact(&p.right_non_membership_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotInFact(br::not_in_fact::NotInFactSearchProofByBuiltinRule::NonMembershipOfUnion(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("NotInFact")),
                ("rule", string("NonMembershipOfUnion")),
            ];
            entries.push(("left_non_membership_proof", project_verify_fact(&p.left_non_membership_proof, runtime)));
            entries.push(("right_non_membership_proof", project_verify_fact(&p.right_non_membership_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotInFact(br::not_in_fact::NotInFactSearchProofByBuiltinRule::NonMembershipOfSetMinusFromRight(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("NotInFact")),
                ("rule", string("NonMembershipOfSetMinusFromRight")),
            ];
            entries.push(("right_membership_proof", project_verify_fact(&p.right_membership_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotInFact(br::not_in_fact::NotInFactSearchProofByBuiltinRule::NonMembershipOfSetMinusFromLeft(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("NotInFact")),
                ("rule", string("NonMembershipOfSetMinusFromLeft")),
            ];
            entries.push(("left_non_membership_proof", project_verify_fact(&p.left_non_membership_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotInFact(br::not_in_fact::NotInFactSearchProofByBuiltinRule::NonMembershipOfIntervalAtOpenEndpoint(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("NotInFact")),
                ("rule", string("NonMembershipOfIntervalAtOpenEndpoint")),
            ];
            entries.push(("endpoint_equal_proof", project_verify_fact(&p.endpoint_equal_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotInFact(br::not_in_fact::NotInFactSearchProofByBuiltinRule::NonMembershipOfIntervalOutside(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("NotInFact")),
                ("rule", string("NonMembershipOfIntervalOutside")),
            ];
            entries.push(("outside_order_proof", project_verify_fact(&p.outside_order_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotIsCartFact(_) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("family", string("NotIsCartFact")),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotIsTupleFact(_) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("family", string("NotIsTupleFact")),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotSubsetFact(br::not_subset::NotSubsetFactSearchProofByBuiltinRule::FromKnownNotSuperset(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("NotSubsetFact")),
                ("rule", string("FromKnownNotSuperset")),
            ];
            entries.push(("cite_fact_id", string(p.cite_fact_id.to_string())));
            if let Some(fact) = runtime.fact_by_id_in_stack(p.cite_fact_id) {
                entries.push(("cite", string(fact.readable_string())));
            }
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotSupersetFact(br::not_superset::NotSupersetFactSearchProofByBuiltinRule::FromKnownNotSubset(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("NotSupersetFact")),
                ("rule", string("FromKnownNotSubset")),
            ];
            entries.push(("cite_fact_id", string(p.cite_fact_id.to_string())));
            if let Some(fact) = runtime.fact_by_id_in_stack(p.cite_fact_id) {
                entries.push(("cite", string(fact.readable_string())));
            }
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NormalAtomicFact(_) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("family", string("NormalAtomicFact")),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotNormalAtomicFact(_) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("family", string("NotNormalAtomicFact")),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::ProperSubsetFact(_) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("family", string("ProperSubsetFact")),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::ProperSupersetFact(_) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("family", string("ProperSupersetFact")),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::DvdFact(_) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("family", string("DvdFact")),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::InjectiveFact(_) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("family", string("InjectiveFact")),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::SurjectiveFact(_) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("family", string("SurjectiveFact")),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::BijectiveFact(_) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("family", string("BijectiveFact")),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::IsChoiceFunctionForFact(_) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("family", string("IsChoiceFunctionForFact")),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotProperSubsetFact(_) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("family", string("NotProperSubsetFact")),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotProperSupersetFact(_) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("family", string("NotProperSupersetFact")),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotDvdFact(_) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("family", string("NotDvdFact")),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotInjectiveFact(_) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("family", string("NotInjectiveFact")),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotSurjectiveFact(_) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("family", string("NotSurjectiveFact")),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotBijectiveFact(_) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("family", string("NotBijectiveFact")),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotIsChoiceFunctionForFact(_) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("family", string("NotIsChoiceFunctionForFact")),
        ]),
    }
}
