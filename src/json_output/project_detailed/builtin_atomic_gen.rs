//! Generated atomic-except-equality builtin-rule detailed projection.
use super::log_algebra_base::project_log_algebra_base;
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
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::AbsDifferenceTriangle(_)) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("rule", string("AbsDifferenceTriangle")),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::MaxLipschitzFromCoordinateBounds(p)) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("rule", string("MaxLipschitzFromCoordinateBounds")),
            ("left_error_bound", project_verify_fact(&p.left_error_bound, runtime)),
            ("right_error_bound", project_verify_fact(&p.right_error_bound, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::MinLipschitzFromCoordinateBounds(p)) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("rule", string("MinLipschitzFromCoordinateBounds")),
            ("left_error_bound", project_verify_fact(&p.left_error_bound, runtime)),
            ("right_error_bound", project_verify_fact(&p.right_error_bound, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(br::in_fact::InFactSearchProofByBuiltinRule::MinPreservesPositiveCarrier(p)) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("rule", string("MinPreservesPositiveCarrier")),
            ("left_positive", project_verify_fact(&p.left_positive, runtime)),
            ("right_positive", project_verify_fact(&p.right_positive, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::ProductNonnegativeNegativeWeak(p)) => object_for(runtime,vec![("type",string("builtin_rule")),("rule",string("ProductNonnegativeNegativeWeak")),
("nonnegative_factor",project_verify_fact(&p.nonnegative_factor,runtime)),
("negative_factor",project_verify_fact(&p.negative_factor,runtime)),
        ]),

        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(br::less::LessFactSearchProofByBuiltinRule::LnNegativeBelowOne(p)) => object_for(runtime,vec![("type",string("builtin_rule")),("rule",string("LnNegativeBelowOne")),
("below_one",super::searched::project_known_premise(&p.below_one,runtime)),
        ]),

        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(br::less::LessFactSearchProofByBuiltinRule::LnPositiveAboveOne(p)) => object_for(runtime,vec![("type",string("builtin_rule")),("rule",string("LnPositiveAboveOne")),
("above_one",super::searched::project_known_premise(&p.above_one,runtime)),
        ]),

        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(br::less::LessFactSearchProofByBuiltinRule::ProductPositiveNegativeStrict(p)) => object_for(runtime,vec![("type",string("builtin_rule")),("rule",string("ProductPositiveNegativeStrict")),
("positive_factor",project_verify_fact(&p.positive_factor,runtime)),
("negative_factor",project_verify_fact(&p.negative_factor,runtime)),
        ]),

        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::SqrtMonotoneFromDefinedRoots(p)) => object_for(runtime,vec![("type",string("builtin_rule")),("rule",string("SqrtMonotoneFromDefinedRoots")),
            ("arguments_order", project_verify_fact(&p.arguments_order,runtime)),
        ]),

        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::AbsFromIntervalBounds(p)) => object_for(runtime,vec![("type",string("builtin_rule")),("rule",string("AbsFromIntervalBounds")),
            ("lower_bound", super::searched::project_known_premise(&p.lower_bound,runtime)),
            ("upper_bound", super::searched::project_known_premise(&p.upper_bound,runtime)),
        ]),

        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::NegationWeakOrder(p)) => object_for(runtime,vec![("type",string("builtin_rule")),("rule",string("NegationWeakOrder")),
            ("argument_order", super::searched::project_known_premise(&p.argument_order,runtime)),
        ]),

        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::IntegerSuccessorGap(p)) => object_for(runtime,vec![("type",string("builtin_rule")),("rule",string("IntegerSuccessorGap")),
            ("left_integer", project_verify_fact(&p.left_integer,runtime)),
            ("right_integer", project_verify_fact(&p.right_integer,runtime)),
            ("strict_order", super::searched::project_known_premise(&p.strict_order,runtime)),
        ]),

        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::LiteralWeakBound(p)) => object_for(runtime,vec![("type",string("builtin_rule")),("rule",string("LiteralWeakBound")),
            ("source_order", super::searched::project_known_premise(&p.source_order,runtime)),
        ]),

        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(br::less::LessFactSearchProofByBuiltinRule::SumStrictOperands(p)) => object_for(runtime,vec![("type",string("builtin_rule")),("rule",string("SumStrictOperands")),
            ("first_order", super::searched::project_known_premise(&p.first_order,runtime)),
            ("second_order", super::searched::project_known_premise(&p.second_order,runtime)),
        ]),

        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(br::less::LessFactSearchProofByBuiltinRule::NegationNegativeFromLiteralBound(p)) => object_for(runtime,vec![("type",string("builtin_rule")),("rule",string("NegationNegativeFromLiteralBound")),
            ("positive_source", super::searched::project_known_premise(&p.positive_source,runtime)),
        ]),

        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(br::less::LessFactSearchProofByBuiltinRule::NegationStrictOrder(p)) => object_for(runtime,vec![("type",string("builtin_rule")),("rule",string("NegationStrictOrder")),
            ("argument_order", super::searched::project_known_premise(&p.argument_order,runtime)),
        ]),

        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotEqualFact(br::not_equal::NotEqualFactSearchProofByBuiltinRule::ProductFactorNonzeroWithZeroAlias(p)) => object_for(runtime,vec![("type",string("builtin_rule")),("rule",string("ProductFactorNonzeroWithZeroAlias")),
            ("product_nonzero", super::searched::project_known_premise(&p.product_nonzero,runtime)),
            ("zero_equality", super::searched::project_equal_searched(&p.zero_equality,runtime)),
        ]),

        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotEqualFact(br::not_equal::NotEqualFactSearchProofByBuiltinRule::EulerNonunit(_)) => object_for(runtime,vec![("type",string("builtin_rule")),("rule",string("EulerNonunit")),
        ]),

        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotEqualFact(br::not_equal::NotEqualFactSearchProofByBuiltinRule::CotNonzeroFromCos(p)) => object_for(runtime,vec![("type",string("builtin_rule")),("rule",string("CotNonzeroFromCos")),
            ("numerator_nonzero", super::searched::project_known_premise(&p.numerator_nonzero,runtime)),
        ]),

        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotEqualFact(br::not_equal::NotEqualFactSearchProofByBuiltinRule::TanNonzeroFromSin(p)) => object_for(runtime,vec![("type",string("builtin_rule")),("rule",string("TanNonzeroFromSin")),
            ("numerator_nonzero", super::searched::project_known_premise(&p.numerator_nonzero,runtime)),
        ]),

        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotEqualFact(br::not_equal::NotEqualFactSearchProofByBuiltinRule::CosNonzeroIntegerPiShift(p)) => object_for(runtime,vec![("type",string("builtin_rule")),("rule",string("CosNonzeroIntegerPiShift")),
            ("source_nonzero", super::searched::project_known_premise(&p.source_nonzero,runtime)),
            ("coefficient", string(p.coefficient.readable_string())),
        ]),

        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotEqualFact(br::not_equal::NotEqualFactSearchProofByBuiltinRule::SinNonzeroIntegerPiShift(p)) => object_for(runtime,vec![("type",string("builtin_rule")),("rule",string("SinNonzeroIntegerPiShift")),
            ("source_nonzero", super::searched::project_known_premise(&p.source_nonzero,runtime)),
            ("coefficient", string(p.coefficient.readable_string())),
        ]),

        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotEqualFact(br::not_equal::NotEqualFactSearchProofByBuiltinRule::CosNonzeroNegation(p)) => object_for(runtime,vec![("type",string("builtin_rule")),("rule",string("CosNonzeroNegation")),
            ("source_nonzero", super::searched::project_known_premise(&p.source_nonzero,runtime)),
        ]),

        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotEqualFact(br::not_equal::NotEqualFactSearchProofByBuiltinRule::SinNonzeroNegation(p)) => object_for(runtime,vec![("type",string("builtin_rule")),("rule",string("SinNonzeroNegation")),
            ("source_nonzero", super::searched::project_known_premise(&p.source_nonzero,runtime)),
        ]),

        AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(br::in_fact::InFactSearchProofByBuiltinRule::NonzeroRationalQuotient(p)) => object_for(runtime, vec![("type", string("builtin_rule")), ("rule", string("NonzeroRationalQuotient")),
            ("numerator_nonzero_rational", project_verify_fact(&p.numerator_nonzero_rational, runtime)),
            ("denominator_nonzero_rational", project_verify_fact(&p.denominator_nonzero_rational, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(br::in_fact::InFactSearchProofByBuiltinRule::NonzeroRationalProduct(p)) => object_for(runtime, vec![("type", string("builtin_rule")), ("rule", string("NonzeroRationalProduct")),
            ("left_nonzero_rational", project_verify_fact(&p.left_nonzero_rational, runtime)),
            ("right_nonzero_rational", project_verify_fact(&p.right_nonzero_rational, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(br::in_fact::InFactSearchProofByBuiltinRule::PositiveRealQuotient(p)) => object_for(runtime, vec![("type", string("builtin_rule")), ("rule", string("PositiveRealQuotient")),
            ("numerator_positive", project_verify_fact(&p.numerator_positive, runtime)),
            ("denominator_positive", project_verify_fact(&p.denominator_positive, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(br::in_fact::InFactSearchProofByBuiltinRule::PositiveRealProduct(p)) => object_for(runtime, vec![("type", string("builtin_rule")), ("rule", string("PositiveRealProduct")),
            ("left_positive", project_verify_fact(&p.left_positive, runtime)),
            ("right_positive", project_verify_fact(&p.right_positive, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::SignLowerBound(_)) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("rule", string("SignLowerBound")),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::SignUpperBound(_)) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("rule", string("SignUpperBound")),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::MinLowerBound(_)) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("rule", string("MinLowerBound")),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::MaxUpperBound(_)) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("rule", string("MaxUpperBound")),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::SignWeakMonotone(p)) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("rule", string("SignWeakMonotone")),
            ("argument_order", project_sign_extremum_order_argument(&p.argument_order, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::MinWeakMonotone(p)) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("rule", string("MinWeakMonotone")),
            ("left_order", project_sign_extremum_order_argument(&p.left_order, runtime)),
            ("right_order", project_sign_extremum_order_argument(&p.right_order, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::MaxWeakMonotone(p)) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("rule", string("MaxWeakMonotone")),
            ("left_order", project_sign_extremum_order_argument(&p.left_order, runtime)),
            ("right_order", project_sign_extremum_order_argument(&p.right_order, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotEqualFact(br::not_equal::NotEqualFactSearchProofByBuiltinRule::ExpNonzero(_)) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("rule", string("ExpNonzero")),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotEqualFact(br::not_equal::NotEqualFactSearchProofByBuiltinRule::FactorialNonzero(_)) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("rule", string("FactorialNonzero")),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotEqualFact(br::not_equal::NotEqualFactSearchProofByBuiltinRule::SignNonzeroFromArgument(p)) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("rule", string("SignNonzeroFromArgument")),
            ("argument_nonzero", super::searched::project_known_premise(&p.argument_nonzero, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotEqualFact(br::not_equal::NotEqualFactSearchProofByBuiltinRule::SignNonzeroReflection(p)) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("rule", string("SignNonzeroReflection")),
            ("real_proof", project_verify_fact(&p.real_proof, runtime)),
            ("sign_nonzero", super::searched::project_known_premise(&p.sign_nonzero, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(br::less::LessFactSearchProofByBuiltinRule::CosPositiveOnOpenHalfPi(p)) => object_for(runtime, vec![("type", string("builtin_rule")), ("family", string("LessFact")), ("rule", string("CosPositiveOnOpenHalfPi")), ("lower_bound", project_verify_fact(&p.lower_bound, runtime)), ("upper_bound", project_verify_fact(&p.upper_bound, runtime))]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(br::less::LessFactSearchProofByBuiltinRule::SinNegativeOnOpenNegativePi(p)) => object_for(runtime, vec![("type", string("builtin_rule")), ("family", string("LessFact")), ("rule", string("SinNegativeOnOpenNegativePi")), ("lower_bound", project_verify_fact(&p.lower_bound, runtime)), ("upper_bound", project_verify_fact(&p.upper_bound, runtime))]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(br::less::LessFactSearchProofByBuiltinRule::TanNegativeOnOpenNegativeHalfPi(p)) => object_for(runtime, vec![("type", string("builtin_rule")), ("family", string("LessFact")), ("rule", string("TanNegativeOnOpenNegativeHalfPi")), ("lower_bound", project_verify_fact(&p.lower_bound, runtime)), ("upper_bound", project_verify_fact(&p.upper_bound, runtime))]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(br::less::LessFactSearchProofByBuiltinRule::CotNegativeOnOpenUpperHalfPi(p)) => object_for(runtime, vec![("type", string("builtin_rule")), ("family", string("LessFact")), ("rule", string("CotNegativeOnOpenUpperHalfPi")), ("lower_bound", project_verify_fact(&p.lower_bound, runtime)), ("upper_bound", project_verify_fact(&p.upper_bound, runtime))]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(br::less::LessFactSearchProofByBuiltinRule::SinPositiveOnFirstQuadrant(p)) => object_for(runtime, vec![("type", string("builtin_rule")), ("family", string("LessFact")), ("rule", string("SinPositiveOnFirstQuadrant")), ("lower_bound", project_verify_fact(&p.lower_bound, runtime)), ("upper_bound", project_verify_fact(&p.upper_bound, runtime))]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(br::less::LessFactSearchProofByBuiltinRule::CosPositiveOnFirstQuadrant(p)) => object_for(runtime, vec![("type", string("builtin_rule")), ("family", string("LessFact")), ("rule", string("CosPositiveOnFirstQuadrant")), ("lower_bound", project_verify_fact(&p.lower_bound, runtime)), ("upper_bound", project_verify_fact(&p.upper_bound, runtime))]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(br::less::LessFactSearchProofByBuiltinRule::CosStrictDecreasingOnClosedPi(p)) => object_for(runtime, vec![("type", string("builtin_rule")), ("family", string("LessFact")), ("rule", string("CosStrictDecreasingOnClosedPi")), ("lower_bound", project_verify_fact(&p.lower_bound, runtime)), ("upper_bound", project_verify_fact(&p.upper_bound, runtime)), ("argument_order", project_verify_fact(&p.argument_order, runtime))]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(br::less::LessFactSearchProofByBuiltinRule::TanStrictIncreasingOnOpenHalfPi(p)) => object_for(runtime, vec![("type", string("builtin_rule")), ("family", string("LessFact")), ("rule", string("TanStrictIncreasingOnOpenHalfPi")), ("lower_bound", project_verify_fact(&p.lower_bound, runtime)), ("upper_bound", project_verify_fact(&p.upper_bound, runtime)), ("argument_order", project_verify_fact(&p.argument_order, runtime))]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(br::less::LessFactSearchProofByBuiltinRule::CotStrictDecreasingOnOpenPi(p)) => object_for(runtime, vec![("type", string("builtin_rule")), ("family", string("LessFact")), ("rule", string("CotStrictDecreasingOnOpenPi")), ("lower_bound", project_verify_fact(&p.lower_bound, runtime)), ("upper_bound", project_verify_fact(&p.upper_bound, runtime)), ("argument_order", project_verify_fact(&p.argument_order, runtime))]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::SinWeakIncreasingOnClosedHalfPi(p)) => object_for(runtime, vec![("type", string("builtin_rule")), ("family", string("LessEqualFact")), ("rule", string("SinWeakIncreasingOnClosedHalfPi")), ("lower_bound", project_verify_fact(&p.lower_bound, runtime)), ("upper_bound", project_verify_fact(&p.upper_bound, runtime)), ("argument_order", project_verify_fact(&p.argument_order, runtime))]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::CosWeakDecreasingOnClosedPi(p)) => object_for(runtime, vec![("type", string("builtin_rule")), ("family", string("LessEqualFact")), ("rule", string("CosWeakDecreasingOnClosedPi")), ("lower_bound", project_verify_fact(&p.lower_bound, runtime)), ("upper_bound", project_verify_fact(&p.upper_bound, runtime)), ("argument_order", project_verify_fact(&p.argument_order, runtime))]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::TanWeakIncreasingOnOpenHalfPi(p)) => object_for(runtime, vec![("type", string("builtin_rule")), ("family", string("LessEqualFact")), ("rule", string("TanWeakIncreasingOnOpenHalfPi")), ("lower_bound", project_verify_fact(&p.lower_bound, runtime)), ("upper_bound", project_verify_fact(&p.upper_bound, runtime)), ("argument_order", project_verify_fact(&p.argument_order, runtime))]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::CotWeakDecreasingOnOpenPi(p)) => object_for(runtime, vec![("type", string("builtin_rule")), ("family", string("LessEqualFact")), ("rule", string("CotWeakDecreasingOnOpenPi")), ("lower_bound", project_verify_fact(&p.lower_bound, runtime)), ("upper_bound", project_verify_fact(&p.upper_bound, runtime)), ("argument_order", project_verify_fact(&p.argument_order, runtime))]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(br::less::LessFactSearchProofByBuiltinRule::MulLeftNegativeReversesStrictLess(p)) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("family", string("LessFact")), ("rule", string("MulLeftNegativeReversesStrictLess")),
            ("factor_sign_proof", project_verify_fact(&p.factor_sign_proof, runtime)),
            ("reversed_order_proof", project_verify_fact(&p.reversed_order_proof, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(br::less::LessFactSearchProofByBuiltinRule::MulRightNegativeReversesStrictLess(p)) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("family", string("LessFact")), ("rule", string("MulRightNegativeReversesStrictLess")),
            ("factor_sign_proof", project_verify_fact(&p.factor_sign_proof, runtime)),
            ("reversed_order_proof", project_verify_fact(&p.reversed_order_proof, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(br::less::LessFactSearchProofByBuiltinRule::MulLeftRightNegativeReversesStrictLess(p)) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("family", string("LessFact")), ("rule", string("MulLeftRightNegativeReversesStrictLess")),
            ("factor_sign_proof", project_verify_fact(&p.factor_sign_proof, runtime)),
            ("reversed_order_proof", project_verify_fact(&p.reversed_order_proof, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(br::less::LessFactSearchProofByBuiltinRule::MulRightLeftNegativeReversesStrictLess(p)) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("family", string("LessFact")), ("rule", string("MulRightLeftNegativeReversesStrictLess")),
            ("factor_sign_proof", project_verify_fact(&p.factor_sign_proof, runtime)),
            ("reversed_order_proof", project_verify_fact(&p.reversed_order_proof, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterFact(br::greater::GreaterFactSearchProofByBuiltinRule::MulLeftNegativeReversesStrictGreater(p)) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("family", string("GreaterFact")), ("rule", string("MulLeftNegativeReversesStrictGreater")),
            ("factor_sign_proof", project_verify_fact(&p.factor_sign_proof, runtime)),
            ("reversed_order_proof", project_verify_fact(&p.reversed_order_proof, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterFact(br::greater::GreaterFactSearchProofByBuiltinRule::MulRightNegativeReversesStrictGreater(p)) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("family", string("GreaterFact")), ("rule", string("MulRightNegativeReversesStrictGreater")),
            ("factor_sign_proof", project_verify_fact(&p.factor_sign_proof, runtime)),
            ("reversed_order_proof", project_verify_fact(&p.reversed_order_proof, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterFact(br::greater::GreaterFactSearchProofByBuiltinRule::MulLeftRightNegativeReversesStrictGreater(p)) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("family", string("GreaterFact")), ("rule", string("MulLeftRightNegativeReversesStrictGreater")),
            ("factor_sign_proof", project_verify_fact(&p.factor_sign_proof, runtime)),
            ("reversed_order_proof", project_verify_fact(&p.reversed_order_proof, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterFact(br::greater::GreaterFactSearchProofByBuiltinRule::MulRightLeftNegativeReversesStrictGreater(p)) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("family", string("GreaterFact")), ("rule", string("MulRightLeftNegativeReversesStrictGreater")),
            ("factor_sign_proof", project_verify_fact(&p.factor_sign_proof, runtime)),
            ("reversed_order_proof", project_verify_fact(&p.reversed_order_proof, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::MulLeftNonpositiveReversesWeakLessEqual(p)) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("family", string("LessEqualFact")), ("rule", string("MulLeftNonpositiveReversesWeakLessEqual")),
            ("factor_sign_proof", project_verify_fact(&p.factor_sign_proof, runtime)),
            ("reversed_order_proof", project_verify_fact(&p.reversed_order_proof, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::MulRightNonpositiveReversesWeakLessEqual(p)) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("family", string("LessEqualFact")), ("rule", string("MulRightNonpositiveReversesWeakLessEqual")),
            ("factor_sign_proof", project_verify_fact(&p.factor_sign_proof, runtime)),
            ("reversed_order_proof", project_verify_fact(&p.reversed_order_proof, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::MulLeftRightNonpositiveReversesWeakLessEqual(p)) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("family", string("LessEqualFact")), ("rule", string("MulLeftRightNonpositiveReversesWeakLessEqual")),
            ("factor_sign_proof", project_verify_fact(&p.factor_sign_proof, runtime)),
            ("reversed_order_proof", project_verify_fact(&p.reversed_order_proof, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::MulRightLeftNonpositiveReversesWeakLessEqual(p)) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("family", string("LessEqualFact")), ("rule", string("MulRightLeftNonpositiveReversesWeakLessEqual")),
            ("factor_sign_proof", project_verify_fact(&p.factor_sign_proof, runtime)),
            ("reversed_order_proof", project_verify_fact(&p.reversed_order_proof, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterEqualFact(br::greater_equal::GreaterEqualFactSearchProofByBuiltinRule::MulLeftNonpositiveReversesWeakGreaterEqual(p)) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("family", string("GreaterEqualFact")), ("rule", string("MulLeftNonpositiveReversesWeakGreaterEqual")),
            ("factor_sign_proof", project_verify_fact(&p.factor_sign_proof, runtime)),
            ("reversed_order_proof", project_verify_fact(&p.reversed_order_proof, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterEqualFact(br::greater_equal::GreaterEqualFactSearchProofByBuiltinRule::MulRightNonpositiveReversesWeakGreaterEqual(p)) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("family", string("GreaterEqualFact")), ("rule", string("MulRightNonpositiveReversesWeakGreaterEqual")),
            ("factor_sign_proof", project_verify_fact(&p.factor_sign_proof, runtime)),
            ("reversed_order_proof", project_verify_fact(&p.reversed_order_proof, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterEqualFact(br::greater_equal::GreaterEqualFactSearchProofByBuiltinRule::MulLeftRightNonpositiveReversesWeakGreaterEqual(p)) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("family", string("GreaterEqualFact")), ("rule", string("MulLeftRightNonpositiveReversesWeakGreaterEqual")),
            ("factor_sign_proof", project_verify_fact(&p.factor_sign_proof, runtime)),
            ("reversed_order_proof", project_verify_fact(&p.reversed_order_proof, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterEqualFact(br::greater_equal::GreaterEqualFactSearchProofByBuiltinRule::MulRightLeftNonpositiveReversesWeakGreaterEqual(p)) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("family", string("GreaterEqualFact")), ("rule", string("MulRightLeftNonpositiveReversesWeakGreaterEqual")),
            ("factor_sign_proof", project_verify_fact(&p.factor_sign_proof, runtime)),
            ("reversed_order_proof", project_verify_fact(&p.reversed_order_proof, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotEqualFact(br::not_equal::NotEqualFactSearchProofByBuiltinRule::CosNonzeroOnFirstQuadrant(p)) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("family", string("NotEqualFact")), ("rule", string("CosNonzeroOnFirstQuadrant")),
            ("lower_bound_proof", super::searched::project_known_premise(&p.lower_bound_proof, runtime)),
            ("upper_bound_proof", super::searched::project_known_premise(&p.upper_bound_proof, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotEqualFact(br::not_equal::NotEqualFactSearchProofByBuiltinRule::SinNonzeroOnFirstQuadrant(p)) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("family", string("NotEqualFact")), ("rule", string("SinNonzeroOnFirstQuadrant")),
            ("lower_bound_proof", super::searched::project_known_premise(&p.lower_bound_proof, runtime)),
            ("upper_bound_proof", super::searched::project_known_premise(&p.upper_bound_proof, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(br::less::LessFactSearchProofByBuiltinRule::TanPositiveOnFirstQuadrant(p)) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("family", string("LessFact")), ("rule", string("TanPositiveOnFirstQuadrant")),
            ("lower_bound_proof", super::searched::project_known_premise(&p.lower_bound_proof, runtime)),
            ("upper_bound_proof", super::searched::project_known_premise(&p.upper_bound_proof, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(br::less::LessFactSearchProofByBuiltinRule::CotPositiveOnFirstQuadrant(p)) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("family", string("LessFact")), ("rule", string("CotPositiveOnFirstQuadrant")),
            ("lower_bound_proof", super::searched::project_known_premise(&p.lower_bound_proof, runtime)),
            ("upper_bound_proof", super::searched::project_known_premise(&p.upper_bound_proof, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterFact(br::greater::GreaterFactSearchProofByBuiltinRule::TanGreaterZeroOnFirstQuadrant(p)) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("family", string("GreaterFact")), ("rule", string("TanGreaterZeroOnFirstQuadrant")),
            ("lower_bound_proof", super::searched::project_known_premise(&p.lower_bound_proof, runtime)),
            ("upper_bound_proof", super::searched::project_known_premise(&p.upper_bound_proof, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterFact(br::greater::GreaterFactSearchProofByBuiltinRule::CotGreaterZeroOnFirstQuadrant(p)) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("family", string("GreaterFact")), ("rule", string("CotGreaterZeroOnFirstQuadrant")),
            ("lower_bound_proof", super::searched::project_known_premise(&p.lower_bound_proof, runtime)),
            ("upper_bound_proof", super::searched::project_known_premise(&p.upper_bound_proof, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(br::less::LessFactSearchProofByBuiltinRule::SinPositiveOnOpenPi(p)) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("family", string("LessFact")), ("rule", string("SinPositiveOnOpenPi")),
            ("lower_bound", project_verify_fact(&p.lower_bound, runtime)),
            ("upper_bound", project_verify_fact(&p.upper_bound, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(br::less::LessFactSearchProofByBuiltinRule::SinStrictMonotoneOnHalfPi(p)) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("family", string("LessFact")), ("rule", string("SinStrictMonotoneOnHalfPi")),
            ("left_lower_bound", project_verify_fact(&p.left_lower_bound, runtime)),
            ("right_upper_bound", project_verify_fact(&p.right_upper_bound, runtime)),
            ("argument_order", project_verify_fact(&p.argument_order, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotEqualFact(br::not_equal::NotEqualFactSearchProofByBuiltinRule::LcmNonzeroFromNonzeroOperands(p)) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("family", string("NotEqualFact")), ("rule", string("LcmNonzeroFromNonzeroOperands")),
            ("first_nonzero", project_verify_fact(&p.first_nonzero, runtime)),
            ("second_nonzero", project_verify_fact(&p.second_nonzero, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotEqualFact(br::not_equal::NotEqualFactSearchProofByBuiltinRule::LogNonzeroFromNonunitArgument(p)) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("family", string("NotEqualFact")), ("rule", string("LogNonzeroFromNonunitArgument")),
            ("base_proof", project_log_algebra_base(&p.base_proof, runtime)),
            ("argument_proof", project_log_algebra_base(&p.argument_proof, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotEqualFact(br::not_equal::NotEqualFactSearchProofByBuiltinRule::PositiveNonunitIntegerPower(p)) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("family", string("NotEqualFact")), ("rule", string("PositiveNonunitIntegerPower")),
            ("base_proof", project_log_algebra_base(&p.base_proof, runtime)),
            ("exponent_integer", project_verify_fact(&p.exponent_integer, runtime)),
            ("exponent_nonzero", project_verify_fact(&p.exponent_nonzero, runtime)),
        ]),

        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(br::less::LessFactSearchProofByBuiltinRule::LogStrictDecreasing(p)) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("family", string("LessFact")), ("rule", string("LogStrictDecreasing")),
            ("guards", object_for(runtime, vec![
                ("base_positive_proof", project_verify_fact(&p.guards.base_positive_proof, runtime)),
                ("base_lt_one_proof", project_verify_fact(&p.guards.base_lt_one_proof, runtime)),
                ("left_arg_positive_proof", project_verify_fact(&p.guards.left_arg_positive_proof, runtime)),
                ("right_arg_positive_proof", project_verify_fact(&p.guards.right_arg_positive_proof, runtime)),
            ])),
            ("argument_order", project_verify_fact(&p.argument_order, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::LogWeakDecreasing(p)) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("family", string("LessEqualFact")), ("rule", string("LogWeakDecreasing")),
            ("guards", object_for(runtime, vec![
                ("base_positive_proof", project_verify_fact(&p.guards.base_positive_proof, runtime)),
                ("base_lt_one_proof", project_verify_fact(&p.guards.base_lt_one_proof, runtime)),
                ("left_arg_positive_proof", project_verify_fact(&p.guards.left_arg_positive_proof, runtime)),
                ("right_arg_positive_proof", project_verify_fact(&p.guards.right_arg_positive_proof, runtime)),
            ])),
            ("argument_order", project_verify_fact(&p.argument_order, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::FloorLowerBound(_)) => object_for(runtime, vec![("type", string("builtin_rule")), ("rule", string("FloorLowerBound"))]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::CeilUpperBound(_)) => object_for(runtime, vec![("type", string("builtin_rule")), ("rule", string("CeilUpperBound"))]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(br::less::LessFactSearchProofByBuiltinRule::FloorStrictUpperBound(_)) => object_for(runtime, vec![("type", string("builtin_rule")), ("rule", string("FloorStrictUpperBound"))]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(br::less::LessFactSearchProofByBuiltinRule::CeilStrictLowerBound(_)) => object_for(runtime, vec![("type", string("builtin_rule")), ("rule", string("CeilStrictLowerBound"))]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(br::less::LessFactSearchProofByBuiltinRule::ExpStrictMonotone(p)) => object_for(runtime,vec![
            ("type",string("builtin_rule")),("rule",string("ExpStrictMonotone")),
            ("argument_order",project_verify_fact(&p.argument_order,runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(br::less::LessFactSearchProofByBuiltinRule::LnStrictMonotone(p)) => object_for(runtime,vec![
            ("type",string("builtin_rule")),("rule",string("LnStrictMonotone")),
            ("argument_order",project_verify_fact(&p.argument_order,runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(br::less::LessFactSearchProofByBuiltinRule::ExpStrictOrderReflection(p)) => object_for(runtime,vec![
            ("type",string("builtin_rule")),("rule",string("ExpStrictOrderReflection")),
            ("image_order",project_verify_fact(&p.image_order,runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(br::less::LessFactSearchProofByBuiltinRule::LnStrictOrderReflection(p)) => object_for(runtime,vec![
            ("type",string("builtin_rule")),("rule",string("LnStrictOrderReflection")),
            ("image_order",project_verify_fact(&p.image_order,runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::ExpWeakMonotone(p)) => object_for(runtime,vec![
            ("type",string("builtin_rule")),("rule",string("ExpWeakMonotone")),
            ("argument_order",project_verify_fact(&p.argument_order,runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::LnWeakMonotone(p)) => object_for(runtime,vec![
            ("type",string("builtin_rule")),("rule",string("LnWeakMonotone")),
            ("argument_order",project_verify_fact(&p.argument_order,runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::ExpWeakOrderReflection(p)) => object_for(runtime,vec![
            ("type",string("builtin_rule")),("rule",string("ExpWeakOrderReflection")),
            ("image_order",project_verify_fact(&p.image_order,runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::LnWeakOrderReflection(p)) => object_for(runtime,vec![
            ("type",string("builtin_rule")),("rule",string("LnWeakOrderReflection")),
            ("image_order",project_verify_fact(&p.image_order,runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::FactorialMonotone(p)) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("rule", string("FactorialMonotone")),
            ("argument_order", project_verify_fact(&p.argument_order, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(br::less::LessFactSearchProofByBuiltinRule::FactorialStrictMonotone(p)) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("rule", string("FactorialStrictMonotone")),
            ("positive_smaller", project_verify_fact(&p.positive_smaller, runtime)),
            ("argument_order", project_verify_fact(&p.argument_order, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::FloorMonotone(p))=> object_for(runtime,vec![("type",string("builtin_rule")),("rule",string("FloorMonotone")),("argument_order",project_verify_fact(&p.argument_order,runtime))]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::CeilMonotone(p))=> object_for(runtime,vec![("type",string("builtin_rule")),("rule",string("CeilMonotone")),("argument_order",project_verify_fact(&p.argument_order,runtime))]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::FiniteSetSumTriangle(_)) => object_for(runtime, vec![("type", string("builtin_rule")), ("rule", string("FiniteSetSumTriangle"))]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::IsFiniteSetFact(br::is_finite_set::IsFiniteSetFactSearchProofByBuiltinRule::FiniteIndexUnion(p)) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("rule", string("FiniteIndexUnion")),
            ("index_finite", project_verify_fact(&p.index_finite, runtime)),
            ("fibres", object_for(runtime, vec![
                ("type", string("by_known_forall_fact")),
                ("fact", string(crate::ast::fact::Fact::ForallFact(p.fibres.fact.clone()).readable_string())),
                ("cite_fact_id", string(p.fibres.cite_fact_id.to_string())),
                ("parameter_renamings", JsonValue::Array(p.fibres.parameter_renamings.iter().map(|r| object_for(runtime, vec![
                    ("source", string(r.source.to_string())), ("target", string(r.target.to_string())),
                ])).collect())),
            ])),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::ComplexTriangle(_))=> object_for(runtime,vec![("type",string("builtin_rule")),("rule",string("ComplexTriangle"))]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::ComplexReverseTriangle(_))=> object_for(runtime,vec![("type",string("builtin_rule")),("rule",string("ComplexReverseTriangle"))]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::LcmCommonMultipleBound(p))=> object_for(runtime,vec![("type",string("builtin_rule")),("rule",string("LcmCommonMultipleBound")),("domains",project_verify_facts(&p.domains,runtime)),("first_multiple",project_verify_fact(&p.first_multiple,runtime)),("second_multiple",project_verify_fact(&p.second_multiple,runtime))]),

        AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterEqualFact(br::greater_equal::GreaterEqualFactSearchProofByBuiltinRule::SumOfNonnegatives(p)) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("family", string("GreaterEqualFact")),
            ("rule", string("SumOfNonnegatives")),
            ("constructor_tree", project_nonnegative_sum_tree(&p.constructor_tree, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterEqualFact(br::greater_equal::GreaterEqualFactSearchProofByBuiltinRule::ClosedSubtractionBound(p)) => project_closed_subtraction_bound("GreaterEqualFact", &p.bound, runtime),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::ClosedSubtractionBound(p)) => project_closed_subtraction_bound("LessEqualFact", &p.bound, runtime),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterEqualFact(br::greater_equal::GreaterEqualFactSearchProofByBuiltinRule::ComplexModulusNonnegative)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::ComplexModulusNonnegative) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("rule", string("ComplexModulusNonnegative")),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotEqualFact(br::not_equal::NotEqualFactSearchProofByBuiltinRule::PeriodicTrigNonzero(p)) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("family", string("NotEqualFact")), ("rule", string("PeriodicTrigNonzero")),
            ("coefficient", string(p.coefficient.readable_string())), ("integer_requirements", project_verify_facts(&p.integer_requirements, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(br::less::LessFactSearchProofByBuiltinRule::FromKnownGreater(p)) => {
            object_for(runtime, vec![
                ("type", string("builtin_rule")), ("family", string("LessFact")),
                ("rule", string("FromKnownGreater")),
                ("premise_proof", super::searched::project_known_premise(&p.premise_proof, runtime)),
            ])
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::FromKnownGreaterEqual(p)) => {
            object_for(runtime, vec![
                ("type", string("builtin_rule")), ("family", string("LessEqualFact")),
                ("rule", string("FromKnownGreaterEqual")),
                ("premise_proof", super::searched::project_known_premise(&p.premise_proof, runtime)),
            ])
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterEqualFact(br::greater_equal::GreaterEqualFactSearchProofByBuiltinRule::FromKnownLessEqual(p)) => {
            object_for(runtime, vec![
                ("type", string("builtin_rule")), ("family", string("GreaterEqualFact")),
                ("rule", string("FromKnownLessEqual")),
                ("premise_proof", super::searched::project_known_premise(&p.premise_proof, runtime)),
            ])
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(br::less::LessFactSearchProofByBuiltinRule::FromKnownOrderComplement(p)) => {
            object_for(runtime, vec![
                ("type", string("builtin_rule")),
                ("family", string("LessFact")),
                ("rule", string("FromKnownOrderComplement")),
                ("premise_proof", super::searched::project_known_premise(&p.premise_proof, runtime)),
                ("real_carrier_proofs", project_verify_facts(&p.real_carrier_proofs, runtime)),
            ])
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterFact(br::greater::GreaterFactSearchProofByBuiltinRule::FromKnownOrderComplement(p)) => {
            object_for(runtime, vec![
                ("type", string("builtin_rule")),
                ("family", string("GreaterFact")),
                ("rule", string("FromKnownOrderComplement")),
                ("premise_proof", super::searched::project_known_premise(&p.premise_proof, runtime)),
                ("real_carrier_proofs", project_verify_facts(&p.real_carrier_proofs, runtime)),
            ])
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::FromKnownOrderComplement(p)) => {
            object_for(runtime, vec![
                ("type", string("builtin_rule")),
                ("family", string("LessEqualFact")),
                ("rule", string("FromKnownOrderComplement")),
                ("premise_proof", super::searched::project_known_premise(&p.premise_proof, runtime)),
                ("real_carrier_proofs", project_verify_facts(&p.real_carrier_proofs, runtime)),
            ])
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterEqualFact(br::greater_equal::GreaterEqualFactSearchProofByBuiltinRule::FromKnownOrderComplement(p)) => {
            object_for(runtime, vec![
                ("type", string("builtin_rule")),
                ("family", string("GreaterEqualFact")),
                ("rule", string("FromKnownOrderComplement")),
                ("premise_proof", super::searched::project_known_premise(&p.premise_proof, runtime)),
                ("real_carrier_proofs", project_verify_facts(&p.real_carrier_proofs, runtime)),
            ])
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotLessFact(br::not_less::NotLessFactSearchProofByBuiltinRule::FromKnownOrderComplement(p)) => {
            object_for(runtime, vec![
                ("type", string("builtin_rule")),
                ("family", string("NotLessFact")),
                ("rule", string("FromKnownOrderComplement")),
                ("premise_proof", super::searched::project_known_premise(&p.premise_proof, runtime)),
                ("real_carrier_proofs", project_verify_facts(&p.real_carrier_proofs, runtime)),
            ])
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotGreaterFact(br::not_greater::NotGreaterFactSearchProofByBuiltinRule::FromKnownOrderComplement(p)) => {
            object_for(runtime, vec![
                ("type", string("builtin_rule")),
                ("family", string("NotGreaterFact")),
                ("rule", string("FromKnownOrderComplement")),
                ("premise_proof", super::searched::project_known_premise(&p.premise_proof, runtime)),
                ("real_carrier_proofs", project_verify_facts(&p.real_carrier_proofs, runtime)),
            ])
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotLessEqualFact(br::not_less_equal::NotLessEqualFactSearchProofByBuiltinRule::FromKnownOrderComplement(p)) => {
            object_for(runtime, vec![
                ("type", string("builtin_rule")),
                ("family", string("NotLessEqualFact")),
                ("rule", string("FromKnownOrderComplement")),
                ("premise_proof", super::searched::project_known_premise(&p.premise_proof, runtime)),
                ("real_carrier_proofs", project_verify_facts(&p.real_carrier_proofs, runtime)),
            ])
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotGreaterEqualFact(br::not_greater_equal::NotGreaterEqualFactSearchProofByBuiltinRule::FromKnownOrderComplement(p)) => {
            object_for(runtime, vec![
                ("type", string("builtin_rule")),
                ("family", string("NotGreaterEqualFact")),
                ("rule", string("FromKnownOrderComplement")),
                ("premise_proof", super::searched::project_known_premise(&p.premise_proof, runtime)),
                ("real_carrier_proofs", project_verify_facts(&p.real_carrier_proofs, runtime)),
            ])
        },
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
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(br::less::LessFactSearchProofByBuiltinRule::FiniteSetSizeProperSubsetLt(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessFact")),
                ("rule", string("FiniteSetSizeProperSubsetLt")),
            ];
            match &p.inclusion_proof {
                br::less::FiniteProperInclusionProof::ByProperSubset { proper_subset_proof } => {
                    entries.push(("route", string("ByProperSubset")));
                    entries.push(("proper_subset_proof", project_verify_fact(proper_subset_proof, runtime)));
                },
                br::less::FiniteProperInclusionProof::BySubsetAndNotEqual { subset_proof, not_equal_proof } => {
                    entries.push(("route", string("BySubsetAndNotEqual")));
                    entries.push(("subset_proof", project_verify_fact(subset_proof, runtime)));
                    entries.push(("not_equal_proof", project_verify_fact(not_equal_proof, runtime)));
                },
            }
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(br::less::LessFactSearchProofByBuiltinRule::PiMultipleComparison(p)) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("family", string("LessFact")), ("rule", string("PiMultipleComparison")),
            ("left_coefficient", string(p.left_coefficient.readable_string())),
            ("right_coefficient", string(p.right_coefficient.readable_string())),
        ]),
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
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(br::less::LessFactSearchProofByBuiltinRule::SubtractPositiveClosedLess(p)) => {
            object_for(runtime, vec![
                ("type", string("builtin_rule")),
                ("family", string("LessFact")),
                ("rule", string("SubtractPositiveClosedLess")),
                ("minuend", string(p.minuend.readable_string())),
                ("subtrahend", string(p.subtrahend.readable_string())),
                ("normalized_subtrahend", string(&p.normalized_subtrahend)),
            ])
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
            entries.push(("base_in_real_proof", project_verify_fact(&p.base_in_real_proof, runtime)));
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
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(br::less::LessFactSearchProofByBuiltinRule::LessFromNegativeDifference(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessFact")),
                ("rule", string("LessFromNegativeDifference")),
            ];
            entries.push(("premise_proof", super::searched::project_known_premise(&p.premise_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(br::less::LessFactSearchProofByBuiltinRule::NegativeDifferenceFromLess(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessFact")),
                ("rule", string("NegativeDifferenceFromLess")),
            ];
            entries.push(("premise_proof", super::searched::project_known_premise(&p.premise_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(br::less::LessFactSearchProofByBuiltinRule::LessFromPosDifference(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessFact")),
                ("rule", string("LessFromPosDifference")),
            ];
            entries.push(("premise_proof", super::searched::project_known_premise(&p.premise_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(br::less::LessFactSearchProofByBuiltinRule::PosDifferenceFromLess(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessFact")),
                ("rule", string("PosDifferenceFromLess")),
            ];
            entries.push(("premise_proof", super::searched::project_known_premise(&p.premise_proof, runtime)));
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
            entries.push(("premise_proof", super::searched::project_known_premise(&p.premise_proof, runtime)));
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
            entries.push(("premise_proof", super::searched::project_known_premise(&p.premise_proof, runtime)));
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
        AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterFact(br::greater::GreaterFactSearchProofByBuiltinRule::NativeEulerGreaterOne(_)) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("family", string("GreaterFact")), ("rule", string("NativeEulerGreaterOne")),
        ]),
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
            entries.push(("premise_proof", super::searched::project_known_premise(&p.premise_proof, runtime)));
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
            entries.push(("premise_proof", super::searched::project_known_premise(&p.premise_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::AbsLeImpliesNegUpper(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessEqualFact")),
                ("rule", string("AbsLeImpliesNegUpper")),
            ];
            entries.push(("premise_proof", super::searched::project_known_premise(&p.premise_proof, runtime)));
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
            entries.push(("base_in_real_proof", project_verify_fact(&p.base_in_real_proof, runtime)));
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
            entries.push(("premise_proof", super::searched::project_known_premise(&p.premise_proof, runtime)));
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
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::LessEqualFromNonpositiveDifference(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessEqualFact")),
                ("rule", string("LessEqualFromNonpositiveDifference")),
            ];
            entries.push(("premise_proof", super::searched::project_known_premise(&p.premise_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::NonpositiveDifferenceFromLessEqual(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessEqualFact")),
                ("rule", string("NonpositiveDifferenceFromLessEqual")),
            ];
            entries.push(("premise_proof", super::searched::project_known_premise(&p.premise_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::LessEqualFromNonnegDifference(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessEqualFact")),
                ("rule", string("LessEqualFromNonnegDifference")),
            ];
            entries.push(("premise_proof", super::searched::project_known_premise(&p.premise_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::NonnegDifferenceFromLessEqual(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("LessEqualFact")),
                ("rule", string("NonnegDifferenceFromLessEqual")),
            ];
            entries.push(("premise_proof", super::searched::project_known_premise(&p.premise_proof, runtime)));
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
        AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(br::less_equal::LessEqualFactSearchProofByBuiltinRule::PositiveCommonDivisorLeGcd(p)) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("family", string("LessEqualFact")),
            ("rule", string("PositiveCommonDivisorLeGcd")),
            ("divisor_in_n_pos_proof", project_verify_fact(&p.divisor_in_n_pos_proof, runtime)),
            ("left_remainder_zero_proof", project_verify_fact(&p.left_remainder_zero_proof, runtime)),
            ("right_remainder_zero_proof", project_verify_fact(&p.right_remainder_zero_proof, runtime)),
        ]),
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
            entries.push(("premise_proof", super::searched::project_known_premise(&p.premise_proof, runtime)));
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
            entries.push(("premise_proof", super::searched::project_known_premise(&p.premise_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterEqualFact(br::greater_equal::GreaterEqualFactSearchProofByBuiltinRule::FromKnownInPositiveNatural(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("GreaterEqualFact")),
                ("rule", string("FromKnownInPositiveNatural")),
            ];
            entries.push(("premise_proof", super::searched::project_known_premise(&p.premise_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterEqualFact(br::greater_equal::GreaterEqualFactSearchProofByBuiltinRule::PredecessorNonNegFromAtLeastOne(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("GreaterEqualFact")),
                ("rule", string("PredecessorNonNegFromAtLeastOne")),
            ];
            entries.push(("at_least_one_proof", super::searched::project_known_premise(&p.at_least_one_proof, runtime)));
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
            entries.push(("premise_proof", super::searched::project_known_premise(&p.premise_proof, runtime)));
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
        AtomicExceptEqualityFactSearchProofByBuiltinRule::IsFiniteSetFact(br::is_finite_set::IsFiniteSetFactSearchProofByBuiltinRule::FunctionRangeOfFiniteDomain(p)) => object_for(runtime,vec![
            ("type",string("builtin_rule")),("family",string("IsFiniteSetFact")),("rule",string("FunctionRangeOfFiniteDomain")),
            ("function_membership",project_verify_fact(&p.function_membership,runtime)),("domain_finite",project_verify_fact(&p.domain_finite,runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::IsFiniteSetFact(br::is_finite_set::IsFiniteSetFactSearchProofByBuiltinRule::SurjectiveImageOfFiniteSet(p)) => object_for(runtime,vec![
            ("type",string("builtin_rule")),("family",string("IsFiniteSetFact")),("rule",string("SurjectiveImageOfFiniteSet")),
            ("cite_surjective_fact_id",string(p.cite_surjective_fact_id.to_string())),
            ("domain_finite_proof",project_verify_fact(&p.domain_finite_proof,runtime)),
        ]),
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
        AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(br::in_fact::InFactSearchProofByBuiltinRule::ClosedExactScalarMembership(p)) => object_for(runtime, vec![
            ("type", string("builtin_rule")),
            ("family", string("InFact")),
            ("rule", string("ClosedExactScalarMembership")),
            ("real_value", string(p.real_value.readable_string())),
            ("imaginary_value", string(p.imaginary_value.readable_string())),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(br::in_fact::InFactSearchProofByBuiltinRule::RealOperandArithmeticClosure(p)) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("family", string("InFact")),
            ("rule", string("RealOperandArithmeticClosure")),
            ("operand_proofs", project_verify_facts(&p.operand_proofs, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(br::in_fact::InFactSearchProofByBuiltinRule::DiscreteArithmeticConstructorClosure(p)) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("family", string("InFact")),
            ("rule", string("DiscreteArithmeticConstructorClosure")),
            ("constructor_tree", project_discrete_arithmetic_constructor_tree(&p.constructor_tree, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(br::in_fact::InFactSearchProofByBuiltinRule::RealArithmeticConstructorClosure(p)) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("family", string("InFact")),
            ("rule", string("RealArithmeticConstructorClosure")),
            ("constructor_tree", project_real_arithmetic_constructor_tree(&p.constructor_tree, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(br::in_fact::InFactSearchProofByBuiltinRule::RealPower(p)) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("family", string("InFact")),
            ("rule", string("RealPower")),
            ("base_in_real_proof", project_verify_fact(&p.base_in_real_proof, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(br::in_fact::InFactSearchProofByBuiltinRule::FiniteSetMaxMember(p)) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("family", string("InFact")),
            ("rule", string("FiniteSetMaxMember")),
            ("set_equal", super::searched::project_equal_searched(&p.set_equal, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(br::in_fact::InFactSearchProofByBuiltinRule::FiniteSetMinMember(p)) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("family", string("InFact")),
            ("rule", string("FiniteSetMinMember")),
            ("set_equal", super::searched::project_equal_searched(&p.set_equal, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(br::in_fact::InFactSearchProofByBuiltinRule::AnonymousFnInDeclaredFnSet(_)) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("family", string("InFact")),
            ("rule", string("AnonymousFnInDeclaredFnSet")),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(br::in_fact::InFactSearchProofByBuiltinRule::PositiveIntegerInNPos(p)) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("family", string("InFact")),
            ("rule", string("PositiveIntegerInNPos")),
            ("integer_proof", project_verify_fact(&p.integer_proof, runtime)),
            ("positive_proof", project_verify_fact(&p.positive_proof, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(br::in_fact::InFactSearchProofByBuiltinRule::IntegerArithmeticClosure(p)) => object_for(runtime,vec![
            ("type",string("builtin_rule")),("family",string("InFact")),("rule",string("IntegerArithmeticClosure")),
            ("operand_proofs",project_verify_facts(&p.operand_proofs,runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(br::in_fact::InFactSearchProofByBuiltinRule::AnonymousFnApplicationScalarCodomain(p)) => object_for(runtime,vec![
            ("type",string("builtin_rule")),("family",string("InFact")),("rule",string("AnonymousFnApplicationScalarCodomain")),
            ("codomain",string(p.codomain.ir().as_str())),
        ]),
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
            entries.push(("source_membership_proof", project_verify_fact(&p.source_membership_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(br::in_fact::InFactSearchProofByBuiltinRule::FoldScalarCodomain(p)) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("family", string("InFact")), ("rule", string("FoldScalarCodomain")),
            ("operation_return_set", string(p.operation_return_set.readable_string())),
            ("codomain", string(p.codomain.ir().as_str())),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(br::in_fact::InFactSearchProofByBuiltinRule::AggregateScalarCodomain(p)) => {
            object_for(runtime, vec![("type", string("builtin_rule")), ("rule", string("AggregateScalarCodomain")),
                ("iterand_return_set", string(p.iterand_return_set.readable_string())), ("codomain", string(format!("{:?}", p.codomain)))])
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(br::in_fact::InFactSearchProofByBuiltinRule::FiniteSetSubsetMembership(p)) => {
            object_for(runtime, vec![
                ("type", string("builtin_rule")),
                ("family", string("InFact")),
                ("rule", string("FiniteSetSubsetMembership")),
                ("source_set", string(p.source_set.ir().as_str().to_string())),
                ("source_membership_proof", project_verify_fact(&p.source_membership_proof, runtime)),
                ("member_in_proofs", project_verify_facts(&p.member_in_proofs, runtime)),
            ])
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
            entries.push(("function_domain", super::function_domain::project_function_domain(&p.domain, runtime)));
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(br::in_fact::InFactSearchProofByBuiltinRule::PowerSetMembership(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("InFact")),
                ("rule", string("PowerSetMembership")),
            ];
            let subset = match &p.subset_proof {
                br::in_fact::PowerSetMembershipSubsetProof::KnownSubset(known) => object_for(runtime, vec![
                    ("type", string("by_known_subset")),
                    ("fact", string(known.fact.readable_string())),
                    ("parent_wd_arguments", string("membership_element_and_power_set_base")),
                    ("searched_proof", super::searched::project_atomic_except_searched(&known.searched_proof, runtime)),
                ]),
                br::in_fact::PowerSetMembershipSubsetProof::VerifiedSubset(proof) =>
                    super::verify::project_atomic_except_success(proof, runtime),
            };
            entries.push(("subset_proof", subset));
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
            entries.push(("in_natural_proof", super::searched::project_known_premise(&p.in_natural_proof, runtime)));
            entries.push(("at_least_one_proof", super::searched::project_known_premise(&p.at_least_one_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(br::in_fact::InFactSearchProofByBuiltinRule::PredecessorFromPositiveNatural(p)) => {
            object_for(runtime, vec![
                ("type", string("builtin_rule")),
                ("family", string("InFact")),
                ("rule", string("PredecessorFromPositiveNatural")),
                ("in_natural_proof", super::searched::project_known_premise(&p.in_natural_proof, runtime)),
                ("positive_proof", super::searched::project_known_premise(&p.positive_proof, runtime)),
            ])
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(br::in_fact::InFactSearchProofByBuiltinRule::PredecessorFromNaturalAboveZero(p)) => {
            object_for(runtime, vec![
                ("type", string("builtin_rule")), ("family", string("InFact")),
                ("rule", string("PredecessorFromNaturalAboveZero")),
                ("in_natural_proof", super::searched::project_known_premise(&p.in_natural_proof, runtime)),
                ("zero_below_proof", super::searched::project_known_premise(&p.zero_below_proof, runtime)),
            ])
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(br::in_fact::InFactSearchProofByBuiltinRule::AnonymousFnApplicationInFnRange(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("InFact")),
                ("rule", string("AnonymousFnApplicationInFnRange")),
            ];
            entries.push(("function_equal", super::searched::project_equal_searched(&p.function_equal, runtime)));
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
        AtomicExceptEqualityFactSearchProofByBuiltinRule::SubsetFact(br::subset::SubsetFactSearchProofByBuiltinRule::FunctionPreimageSubsetOfInputCarrier(p)) => {
            object_for(runtime, vec![
                ("type", string("builtin_rule")),
                ("family", string("SubsetFact")),
                ("rule", string("FunctionPreimageSubsetOfInputCarrier")),
                ("construction", super::wd_by_def::project_preimage_construction(&p.construction, runtime)),
                ("carrier_match", super::searched::project_equal_searched(&p.carrier_match, runtime)),
            ])
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
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotEqualFact(br::not_equal::NotEqualFactSearchProofByBuiltinRule::PiNonzero(_)) => {
            object_for(runtime, vec![("type", string("builtin_rule")), ("rule", string("PiNonzero"))])
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotEqualFact(br::not_equal::NotEqualFactSearchProofByBuiltinRule::ImaginaryUnitNonzero(_)) => {
            object_for(runtime, vec![("type", string("builtin_rule")), ("rule", string("ImaginaryUnitNonzero"))])
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
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotEqualFact(br::not_equal::NotEqualFactSearchProofByBuiltinRule::ClosedRational(p)) => {
            object_for(runtime, vec![
                ("type", string("builtin_rule")), ("rule", string("ClosedRational")),
                ("left_normal", string(p.left_normal.readable_string())),
                ("right_normal", string(p.right_normal.readable_string())),
            ])
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotEqualFact(br::not_equal::NotEqualFactSearchProofByBuiltinRule::ClosedComplex(p)) => {
            object_for(runtime, vec![
                ("type", string("builtin_rule")), ("family", string("NotEqualFact")),
                ("rule", string("ClosedComplex")),
                ("left_real", string(p.left_real.readable_string())),
                ("left_imaginary", string(p.left_imaginary.readable_string())),
                ("right_real", string(p.right_real.readable_string())),
                ("right_imaginary", string(p.right_imaginary.readable_string())),
            ])
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotEqualFact(br::not_equal::NotEqualFactSearchProofByBuiltinRule::NotEqualSymmetry(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("NotEqualFact")),
                ("rule", string("NotEqualSymmetry")),
            ];
            entries.push(("premise_proof", super::searched::project_known_premise(&p.premise_proof, runtime)));
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
            entries.push(("premise_proof", super::searched::project_known_premise(&p.premise_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotEqualFact(br::not_equal::NotEqualFactSearchProofByBuiltinRule::CosNonzeroOnOpenHalfPi(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("NotEqualFact")),
                ("rule", string("CosNonzeroOnOpenHalfPi")),
            ];
            entries.push(("lower_bound_proof", super::searched::project_known_premise(&p.lower_bound_proof, runtime)));
            entries.push(("upper_bound_proof", super::searched::project_known_premise(&p.upper_bound_proof, runtime)));
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
            entries.push(("lower_bound_proof", super::searched::project_known_premise(&p.lower_bound_proof, runtime)));
            entries.push(("upper_bound_proof", super::searched::project_known_premise(&p.upper_bound_proof, runtime)));
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
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotEqualFact(br::not_equal::NotEqualFactSearchProofByBuiltinRule::InequalityFromDifferenceNonzero(p)) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("family", string("NotEqualFact")), ("rule", string("InequalityFromDifferenceNonzero")),
            ("premise_proof", super::searched::project_known_premise(&p.premise_proof, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotEqualFact(br::not_equal::NotEqualFactSearchProofByBuiltinRule::InequalityFromSumNonzero(p)) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("family", string("NotEqualFact")), ("rule", string("InequalityFromSumNonzero")),
            ("premise_proof", super::searched::project_known_premise(&p.premise_proof, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotEqualFact(br::not_equal::NotEqualFactSearchProofByBuiltinRule::ComplexModulusNonzero(p)) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("family", string("NotEqualFact")), ("rule", string("ComplexModulusNonzero")),
            ("arg_nonzero_proof", project_verify_fact(&p.arg_nonzero_proof, runtime)),
        ]),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotEqualFact(br::not_equal::NotEqualFactSearchProofByBuiltinRule::NonzeroFromSignedBound(p)) => object_for(runtime,vec![
            ("type",string("builtin_rule")),("family",string("NotEqualFact")),("rule",string("NonzeroFromSignedBound")),
            ("cite_fact_id",string(p.cite_fact_id.to_string())),
        ]),
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
            entries.push(("product_nonzero_proof", super::searched::project_known_premise(&p.product_nonzero_proof, runtime)));
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
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
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
            entries.push(("premise_proof", super::searched::project_known_premise(&p.premise_proof, runtime)));
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
            entries.push(("premise_proof", super::searched::project_known_premise(&p.premise_proof, runtime)));
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
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotSubsetFact(br::not_subset::NotSubsetFactSearchProofByBuiltinRule::FromKnownNotSuperset(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("NotSubsetFact")),
                ("rule", string("FromKnownNotSuperset")),
            ];
            entries.push(("premise_proof", super::searched::project_known_premise(&p.premise_proof, runtime)));
            object_for(runtime, entries)
        },
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotSupersetFact(br::not_superset::NotSupersetFactSearchProofByBuiltinRule::FromKnownNotSubset(p)) => {
            let mut entries = vec![
                ("type", string("builtin_rule")),
                ("family", string("NotSupersetFact")),
                ("rule", string("FromKnownNotSubset")),
            ];
            entries.push(("premise_proof", super::searched::project_known_premise(&p.premise_proof, runtime)));
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

fn project_closed_subtraction_bound(
    family: &str,
    p: &br::closed_subtraction_bound::ClosedSubtractionBoundCertificate,
    runtime: &Runtime,
) -> JsonValue {
    object_for(
        runtime,
        vec![
            ("type", string("builtin_rule")),
            ("family", string(family)),
            ("rule", string("ClosedSubtractionBound")),
            (
                "bound",
                object_for(
                    runtime,
                    vec![
                        ("cite_fact_id", string(p.cite_fact_id.to_string())),
                        ("cite", string(p.source_fact.readable_string())),
                        (
                            "direction",
                            string(match p.direction {
                                br::closed_subtraction_bound::BoundDirection::Lower => "lower",
                                br::closed_subtraction_bound::BoundDirection::Upper => "upper",
                            }),
                        ),
                        (
                            "normalized_subtrahend",
                            string(p.normalized_subtrahend.readable_string()),
                        ),
                        (
                            "translated_bound",
                            string(p.translated_bound.readable_string()),
                        ),
                        ("target_bound", string(p.target_bound.readable_string())),
                    ],
                ),
            ),
        ],
    )
}

fn project_real_arithmetic_constructor_tree(
    tree: &br::in_fact::RealArithmeticConstructorTree,
    runtime: &Runtime,
) -> JsonValue {
    use br::in_fact::RealArithmeticConstructorTree::*;
    let terminal = |proof: &br::in_fact::RealArithmeticConstructorTerminalProof| {
        object_for(
            runtime,
            vec![
                (
                    "fact",
                    string(format!(
                        "{} $in {}",
                        proof.fact.element.readable_string(),
                        proof.fact.set.readable_string()
                    )),
                ),
                (
                    "searched_proof",
                    super::searched::project_atomic_except_searched(&proof.searched_proof, runtime),
                ),
            ],
        )
    };
    let binary = |kind, left, right| {
        object_for(
            runtime,
            vec![
                ("constructor", string(kind)),
                (
                    "left",
                    project_real_arithmetic_constructor_tree(left, runtime),
                ),
                (
                    "right",
                    project_real_arithmetic_constructor_tree(right, runtime),
                ),
            ],
        )
    };
    match tree {
        Leaf(proof) => object_for(
            runtime,
            vec![("constructor", string("leaf")), ("proof", terminal(proof))],
        ),
        Add { left, right } => binary("add", left, right),
        Sub { left, right } => binary("sub", left, right),
        Neg { argument } => object_for(
            runtime,
            vec![
                ("constructor", string("neg")),
                (
                    "argument",
                    project_real_arithmetic_constructor_tree(argument, runtime),
                ),
            ],
        ),
        Mul { left, right } => binary("mul", left, right),
        Div { left, right } => binary("div", left, right),
        IntegerPow {
            base,
            exponent_in_integer_proof,
        } => object_for(
            runtime,
            vec![
                ("constructor", string("integer_pow")),
                (
                    "base",
                    project_real_arithmetic_constructor_tree(base, runtime),
                ),
                (
                    "exponent_in_integer_proof",
                    terminal(exponent_in_integer_proof),
                ),
            ],
        ),
    }
}

fn project_discrete_arithmetic_constructor_tree(
    tree: &br::in_fact::DiscreteArithmeticConstructorTree,
    runtime: &Runtime,
) -> JsonValue {
    use br::in_fact::DiscreteArithmeticConstructorTree::*;
    let binary = |kind, left, right| {
        object_for(
            runtime,
            vec![
                ("constructor", string(kind)),
                (
                    "left",
                    project_discrete_arithmetic_constructor_tree(left, runtime),
                ),
                (
                    "right",
                    project_discrete_arithmetic_constructor_tree(right, runtime),
                ),
            ],
        )
    };
    match tree {
        Leaf {
            fact,
            searched_proof,
        } => object_for(
            runtime,
            vec![
                ("constructor", string("leaf")),
                (
                    "fact",
                    string(format!(
                        "{} $in {}",
                        fact.element.readable_string(),
                        fact.set.readable_string()
                    )),
                ),
                (
                    "searched_proof",
                    super::searched::project_atomic_except_searched(searched_proof, runtime),
                ),
            ],
        ),
        Add { left, right } => binary("add", left, right),
        Sub { left, right } => binary("sub", left, right),
        Mul { left, right } => binary("mul", left, right),
        Neg { argument } => object_for(
            runtime,
            vec![
                ("constructor", string("neg")),
                (
                    "argument",
                    project_discrete_arithmetic_constructor_tree(argument, runtime),
                ),
            ],
        ),
    }
}

fn project_nonnegative_sum_tree(
    tree: &br::greater_equal::NonnegativeSumTree,
    runtime: &Runtime,
) -> JsonValue {
    use br::greater_equal::NonnegativeSumTree::*;
    match tree {
        Leaf(proof) => object_for(
            runtime,
            vec![
                ("constructor", string("leaf")),
                ("proof", project_verify_fact(proof, runtime)),
            ],
        ),
        Add { left, right } => object_for(
            runtime,
            vec![
                ("constructor", string("add")),
                ("left", project_nonnegative_sum_tree(left, runtime)),
                ("right", project_nonnegative_sum_tree(right, runtime)),
            ],
        ),
    }
}

fn project_sign_extremum_order_argument(
    proof: &br::sign_extremum_order::WeakOrderArgumentProof,
    runtime: &Runtime,
) -> JsonValue {
    match proof {
        br::sign_extremum_order::WeakOrderArgumentProof::SameArgument(argument) => object_for(
            runtime,
            vec![
                ("type", string("same_argument")),
                ("argument", string(argument.readable_string())),
            ],
        ),
        br::sign_extremum_order::WeakOrderArgumentProof::ByOrder(proof) => {
            project_verify_fact(proof, runtime)
        }
    }
}
