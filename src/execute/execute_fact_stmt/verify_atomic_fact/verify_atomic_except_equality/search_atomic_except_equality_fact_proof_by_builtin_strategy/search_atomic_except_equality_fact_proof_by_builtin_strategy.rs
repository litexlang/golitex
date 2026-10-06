use super::helper::{enter_strategy_goal, leave_strategy_goal, strategy_goal_key};
use super::result::AtomicExceptEqualityFactSearchProofByBuiltinStrategy;
use crate::ast::fact::AtomicFact;
use crate::execute::execute_fact_stmt::verify_state::VerifyState;
use crate::runtime::{Runtime, RuntimeResult};

impl Runtime {
    pub fn search_atomic_except_equality_fact_proof_by_builtin_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: VerifyState,
    ) -> RuntimeResult<Option<AtomicExceptEqualityFactSearchProofByBuiltinStrategy>> {
        // Literal tuple struct membership is skipped here (depends on struct-env APIs).
        // Prefer CartMembership for cartesian constructors.

        let goal_key = strategy_goal_key(fact);
        if !enter_strategy_goal(&goal_key) {
            return Ok(None);
        }
        let result =
            self.search_atomic_except_equality_fact_proof_by_builtin_strategy_inner(fact, ctx);
        leave_strategy_goal(&goal_key);
        result
    }

    fn search_atomic_except_equality_fact_proof_by_builtin_strategy_inner(
        &mut self,
        fact: &AtomicFact,
        ctx: VerifyState,
    ) -> RuntimeResult<Option<AtomicExceptEqualityFactSearchProofByBuiltinStrategy>> {
        if let Some(proof) = self.search_finite_function_application_membership_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::FiniteFunctionApplicationMembership(proof)));
        }
        if let Some(proof) = self.search_function_set_membership_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::FunctionSetMembership(proof)));
        }
        if let Some(proof) = self.search_literal_tuple_projection_membership_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::LiteralTupleProjectionMembership(proof)));
        }
        // nonzero (NotEqual)
        if let Some(proof) = self.search_nonzero_product_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::NonzeroProduct(proof)));
        }

        // additive_sign
        if let Some(proof) = self.search_pos_add_pos_is_pos_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::PosAddPosIsPos(proof)));
        }
        if let Some(proof) = self.search_nonnegative_sum_is_nonnegative_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::NonnegativeSumIsNonnegative(proof)));
        }
        if let Some(proof) = self.search_strict_additive_left_strict_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::StrictAdditiveLeftStrict(proof)));
        }
        if let Some(proof) = self.search_strict_additive_right_strict_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::StrictAdditiveRightStrict(proof)));
        }

        // structural_order_weak
        if let Some(proof) = self.search_finite_set_max_list_members_less_equal_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::FiniteSetMaxListMembersLessEqual(proof)));
        }
        if let Some(proof) = self.search_finite_set_max_constructor_parts_less_equal_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::FiniteSetMaxConstructorPartsLessEqual(proof)));
        }
        if let Some(proof) = self.search_finite_set_min_list_members_less_equal_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::FiniteSetMinListMembersLessEqual(proof)));
        }
        if let Some(proof) = self.search_finite_set_min_constructor_parts_less_equal_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::FiniteSetMinConstructorPartsLessEqual(proof)));
        }
        if let Some(proof) = self.search_product_nonnegative_both_nonneg_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::ProductNonnegativeBothNonneg(proof)));
        }
        if let Some(proof) = self.search_product_nonnegative_both_nonpos_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::ProductNonnegativeBothNonpos(proof)));
        }
        if let Some(proof) = self.search_add_componentwise_less_equal_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::AddComponentwiseLessEqual(proof)));
        }
        if let Some(proof) = self.search_add_crossed_less_equal_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::AddCrossedLessEqual(proof)));
        }
        if let Some(proof) = self.search_sub_shared_subtrahend_less_equal_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::SubSharedSubtrahendLessEqual(proof)));
        }
        if let Some(proof) = self.search_sub_shared_minuend_less_equal_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::SubSharedMinuendLessEqual(proof)));
        }
        if let Some(proof) = self.search_div_shared_positive_denom_less_equal_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::DivSharedPositiveDenomLessEqual(proof)));
        }
        if let Some(proof) = self.search_div_shared_negative_denom_less_equal_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::DivSharedNegativeDenomLessEqual(proof)));
        }
        if let Some(proof) = self.search_pow_shared_exponent_less_equal_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::PowSharedExponentLessEqual(proof)));
        }
        if let Some(proof) = self.search_abs_vs_square_less_equal_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::AbsVsSquareLessEqual(proof)));
        }
        if let Some(proof) = self.search_add_right_nonnegative_shift_left_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::AddRightNonnegativeShiftLeft(proof)));
        }
        if let Some(proof) = self.search_add_right_nonnegative_shift_right_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::AddRightNonnegativeShiftRight(proof)));
        }
        if let Some(proof) = self.search_add_left_nonpositive_shift_left_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::AddLeftNonpositiveShiftLeft(proof)));
        }
        if let Some(proof) = self.search_add_left_nonpositive_shift_right_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::AddLeftNonpositiveShiftRight(proof)));
        }
        if let Some(proof) = self.search_sub_nonpositive_to_zero_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::SubNonpositiveToZero(proof)));
        }
        if let Some(proof) = self.search_sub_nonnegative_from_zero_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::SubNonnegativeFromZero(proof)));
        }
        if let Some(proof) = self.search_mul_scale_factor_one_or_more_right_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::MulScaleFactorOneOrMoreRight(proof)));
        }
        if let Some(proof) = self.search_mul_scale_factor_one_or_less_left_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::MulScaleFactorOneOrLessLeft(proof)));
        }
        if let Some(proof) = self.search_mul_componentwise_less_equal_aligned_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::MulComponentwiseLessEqualAligned(proof)));
        }
        if let Some(proof) = self.search_mul_componentwise_less_equal_crossed_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::MulComponentwiseLessEqualCrossed(proof)));
        }
        if let Some(proof) = self.search_common_nonnegative_factor_less_equal_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::CommonNonnegativeFactorLessEqual(proof)));
        }

        // structural_order_strict
        if let Some(proof) = self.search_product_positive_both_pos_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::ProductPositiveBothPos(proof)));
        }
        if let Some(proof) = self.search_product_positive_both_neg_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::ProductPositiveBothNeg(proof)));
        }
        if let Some(proof) = self.search_quotient_positive_same_sign_pos_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::QuotientPositiveSameSignPos(proof)));
        }
        if let Some(proof) = self.search_quotient_positive_same_sign_neg_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::QuotientPositiveSameSignNeg(proof)));
        }
        if let Some(proof) = self.search_add_componentwise_strict_left_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::AddComponentwiseStrictLeft(proof)));
        }
        if let Some(proof) = self.search_add_componentwise_strict_right_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::AddComponentwiseStrictRight(proof)));
        }
        if let Some(proof) = self.search_sub_shared_subtrahend_less_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::SubSharedSubtrahendLess(proof)));
        }
        if let Some(proof) = self.search_sub_shared_minuend_less_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::SubSharedMinuendLess(proof)));
        }
        if let Some(proof) = self.search_div_shared_positive_denom_less_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::DivSharedPositiveDenomLess(proof)));
        }
        if let Some(proof) = self.search_div_shared_negative_denom_less_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::DivSharedNegativeDenomLess(proof)));
        }
        if let Some(proof) = self.search_pow_shared_exponent_less_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::PowSharedExponentLess(proof)));
        }
        if let Some(proof) = self.search_abs_vs_square_less_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::AbsVsSquareLess(proof)));
        }
        if let Some(proof) = self.search_add_right_strict_shift_left_strict_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::AddRightStrictShiftLeftStrict(proof)));
        }
        if let Some(proof) = self.search_add_right_strict_shift_left_weak_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::AddRightStrictShiftLeftWeak(proof)));
        }
        if let Some(proof) = self.search_add_right_strict_shift_right_strict_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::AddRightStrictShiftRightStrict(proof)));
        }
        if let Some(proof) = self.search_add_right_strict_shift_right_weak_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::AddRightStrictShiftRightWeak(proof)));
        }
        if let Some(proof) = self.search_sub_positive_to_zero_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::SubPositiveToZero(proof)));
        }
        if let Some(proof) = self.search_sub_positive_from_zero_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::SubPositiveFromZero(proof)));
        }
        if let Some(proof) = self.search_common_positive_factor_less_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::CommonPositiveFactorLess(proof)));
        }

        // numeric_carrier (In StandardSet)
        if let Some(proof) = self.search_finite_set_size_in_numeric_carrier_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::FiniteSetSizeInNumericCarrier(proof)));
        }
        if let Some(proof) = self.search_finite_extremum_source_in_carrier_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::FiniteExtremumSourceInCarrier(proof)));
        }
        if let Some(proof) = self.search_refined_numeric_carrier_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::RefinedNumericCarrier(proof)));
        }
        if let Some(proof) = self.search_real_arithmetic_carrier_closure_add_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::RealArithmeticCarrierClosureAdd(proof)));
        }
        if let Some(proof) = self.search_real_arithmetic_carrier_closure_sub_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::RealArithmeticCarrierClosureSub(proof)));
        }
        if let Some(proof) = self.search_real_arithmetic_carrier_closure_mul_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::RealArithmeticCarrierClosureMul(proof)));
        }
        if let Some(proof) = self.search_real_arithmetic_carrier_closure_div_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::RealArithmeticCarrierClosureDiv(proof)));
        }
        if let Some(proof) = self.search_real_arithmetic_carrier_closure_pow_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::RealArithmeticCarrierClosurePow(proof)));
        }
        if let Some(proof) = self.search_rational_arithmetic_carrier_closure_add_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::RationalArithmeticCarrierClosureAdd(proof)));
        }
        if let Some(proof) = self.search_rational_arithmetic_carrier_closure_sub_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::RationalArithmeticCarrierClosureSub(proof)));
        }
        if let Some(proof) = self.search_rational_arithmetic_carrier_closure_mul_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::RationalArithmeticCarrierClosureMul(proof)));
        }
        if let Some(proof) = self.search_rational_arithmetic_carrier_closure_div_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::RationalArithmeticCarrierClosureDiv(proof)));
        }
        if let Some(proof) = self.search_rational_arithmetic_carrier_closure_pow_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::RationalArithmeticCarrierClosurePow(proof)));
        }
        if let Some(proof) = self.search_rational_arithmetic_carrier_closure_abs_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::RationalArithmeticCarrierClosureAbs(proof)));
        }
        if let Some(proof) = self.search_field_arithmetic_carrier_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::FieldArithmeticCarrierClosure(proof)));
        }
        if let Some(proof) = self.search_integer_arithmetic_carrier_closure_add_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::IntegerArithmeticCarrierClosureAdd(proof)));
        }
        if let Some(proof) = self.search_integer_arithmetic_carrier_closure_sub_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::IntegerArithmeticCarrierClosureSub(proof)));
        }
        if let Some(proof) = self.search_integer_arithmetic_carrier_closure_mul_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::IntegerArithmeticCarrierClosureMul(proof)));
        }
        if let Some(proof) = self.search_integer_arithmetic_carrier_closure_mod_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::IntegerArithmeticCarrierClosureMod(proof)));
        }
        if let Some(proof) = self.search_integer_arithmetic_carrier_closure_pow_nat_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::IntegerArithmeticCarrierClosurePowNat(proof)));
        }
        if let Some(proof) = self.search_integer_arithmetic_carrier_closure_abs_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::IntegerArithmeticCarrierClosureAbs(proof)));
        }
        if let Some(proof) = self.search_natural_arithmetic_carrier_closure_add_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::NaturalArithmeticCarrierClosureAdd(proof)));
        }
        if let Some(proof) = self.search_natural_arithmetic_carrier_closure_mul_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::NaturalArithmeticCarrierClosureMul(proof)));
        }
        if let Some(proof) = self.search_natural_arithmetic_carrier_closure_sub_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::NaturalArithmeticCarrierClosureSub(proof)));
        }
        if let Some(proof) = self.search_natural_arithmetic_carrier_closure_pow_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::NaturalArithmeticCarrierClosurePow(proof)));
        }
        if let Some(proof) = self.search_natural_arithmetic_carrier_closure_abs_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::NaturalArithmeticCarrierClosureAbs(proof)));
        }
        if let Some(proof) = self.search_positive_natural_carrier_add_left_pos_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::PositiveNaturalCarrierAddLeftPos(proof)));
        }
        if let Some(proof) = self.search_positive_natural_carrier_add_right_pos_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::PositiveNaturalCarrierAddRightPos(proof)));
        }
        if let Some(proof) = self.search_positive_natural_carrier_mul_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::PositiveNaturalCarrierMul(proof)));
        }
        if let Some(proof) = self.search_positive_natural_carrier_pow_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::PositiveNaturalCarrierPow(proof)));
        }
        if let Some(proof) = self.search_positive_natural_carrier_abs_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::PositiveNaturalCarrierAbs(proof)));
        }
        if let Some(proof) = self.search_positive_natural_carrier_finite_set_size_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::PositiveNaturalCarrierFiniteSetSize(proof)));
        }

        // Displayed membership and nonmembership remove one list constructor.
        if let Some(proof) = self.search_list_set_membership_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::ListSetMembership(proof)));
        }
        if let Some(proof) = self.search_list_set_nonmembership_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::ListSetNonMembership(proof)));
        }

        // set_membership (In)
        if let Some(proof) = self.search_cart_membership_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::CartMembership(proof)));
        }
        if let Some(proof) = self.search_union_membership_from_left_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::UnionMembershipFromLeft(proof)));
        }
        if let Some(proof) = self.search_union_membership_from_right_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::UnionMembershipFromRight(proof)));
        }
        if let Some(proof) = self.search_intersect_membership_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::IntersectMembership(proof)));
        }
        if let Some(proof) = self.search_set_minus_membership_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::SetMinusMembership(proof)));
        }
        if let Some(proof) = self.search_power_set_membership_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::PowerSetMembership(proof)));
        }
        if let Some(proof) = self.search_range_membership_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::RangeMembership(proof)));
        }
        if let Some(proof) = self.search_closed_range_membership_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::ClosedRangeMembership(proof)));
        }
        if let Some(proof) = self.search_interval_membership_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::IntervalMembership(proof)));
        }
        if let Some(proof) = self.search_set_builder_membership_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::SetBuilderMembership(proof)));
        }
        // `$in R` / `$in cart(...)` from have-fn return, then ⊂-lift to `$in C`.
        if let Some(proof) = self.search_fn_application_in_codomain_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::FnApplicationInCodomain(proof)));
        }
        if let Some(proof) = self.search_standard_set_subset_membership_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::StandardSetSubsetMembership(proof)));
        }

        // subset / flipped superset
        if let Some(proof) = self.search_list_set_subset_from_members_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::ListSetSubsetFromMembers(proof)));
        }
        if let Some(proof) = self.search_union_subset_from_both_operands_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::UnionSubsetFromBothOperands(proof)));
        }
        if let Some(proof) = self.search_intersect_subset_from_left_operand_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::IntersectSubsetFromLeftOperand(proof)));
        }
        if let Some(proof) = self.search_intersect_subset_from_right_operand_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::IntersectSubsetFromRightOperand(proof)));
        }
        if let Some(proof) = self.search_set_minus_subset_from_left_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::SetMinusSubsetFromLeft(proof)));
        }
        if let Some(proof) = self.search_subset_of_intersect_from_both_bounds_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::SubsetOfIntersectFromBothBounds(proof)));
        }

        // is_finite_set
        if let Some(proof) = self.search_fn_range_finite_from_domain_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::FnRangeFiniteFromDomain(proof)));
        }
        if let Some(proof) = self.search_power_set_finite_from_base_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::PowerSetFiniteFromBase(proof)));
        }
        if let Some(proof) = self.search_set_builder_finite_from_param_set_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::SetBuilderFiniteFromParamSet(proof)));
        }
        if let Some(proof) = self.search_union_finite_from_both_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::UnionFiniteFromBoth(proof)));
        }
        if let Some(proof) = self.search_intersect_finite_from_both_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::IntersectFiniteFromBoth(proof)));
        }
        if let Some(proof) = self.search_set_minus_finite_from_left_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::SetMinusFiniteFromLeft(proof)));
        }
        if let Some(proof) = self.search_cart_finite_from_factors_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::CartFiniteFromFactors(proof)));
        }
        if let Some(proof) = self.search_subset_of_finite_set_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::SubsetOfFiniteSet(proof)));
        }

        // is_nonempty_set
        if let Some(proof) = self.search_closed_range_nonempty_from_endpoint_order_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::ClosedRangeNonemptyFromEndpointOrder(proof)));
        }
        if let Some(proof) = self.search_range_nonempty_from_endpoint_order_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::RangeNonemptyFromEndpointOrder(proof)));
        }
        if let Some(proof) = self.search_interval_nonempty_from_endpoint_order_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::IntervalNonemptyFromEndpointOrder(proof)));
        }
        if let Some(proof) = self.search_union_nonempty_from_left_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::UnionNonemptyFromLeft(proof)));
        }
        if let Some(proof) = self.search_union_nonempty_from_right_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::UnionNonemptyFromRight(proof)));
        }
        if let Some(proof) = self.search_cart_nonempty_from_all_factors_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::CartNonemptyFromAllFactors(proof)));
        }
        if let Some(proof) = self.search_function_space_nonempty_from_empty_domain_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::FunctionSpaceNonemptyFromEmptyDomain(proof)));
        }
        if let Some(proof) = self.search_fn_set_nonempty_from_codomain_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::FnSetNonemptyFromCodomain(proof)));
        }
        if let Some(proof) = self.search_function_graph_nonempty_from_domain_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::FunctionGraphNonemptyFromDomain(proof)));
        }
        if let Some(proof) = self.search_finite_seq_set_nonempty_from_codomain_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::FiniteSeqSetNonemptyFromCodomain(proof)));
        }
        if let Some(proof) = self.search_seq_set_nonempty_from_codomain_strategy(fact, ctx)? {
            return Ok(Some(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::SeqSetNonemptyFromCodomain(proof)));
        }

        Ok(None)
    }
}
