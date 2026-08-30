//! Arithmetic builtin-rule identifiers.

/// Stable identities for arithmetic/order rules whose complete certificate is
/// the target fact plus the recursively checked ordered premise list.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ArithmeticBuiltinRule {
    /// Ordered numeric transitivity. The enclosing result retains the
    /// verifier-owned carrier checks followed by the two ordered premises.
    OrderTransitivity,
    LessEqualFromStrictOrder,
    GreaterEqualFromStrictOrder,
    SubNonnegativeFromLessEqual,
    SubPositiveFromLess,
    /// From `a - b < c`, conclude `a < b + c` (up to the checked
    /// commutativity of the target addition).
    SubLessImpliesLessAdd,
    /// From `a - b < c`, conclude `a - c < b`.
    SubLessSwap,
    /// Weak counterpart of `SubLessSwap`: from `a - b <= c`, conclude
    /// `a - c <= b`.
    SubLessEqualSwap,
    /// From `a <= b + c`, conclude `a - c <= b`, accepting the checked
    /// commutative orientation of the target sum.
    LessEqualAddImpliesSubLessEqual,
    /// Negating both sides reverses a strict or weak real order. The
    /// enclosing Result retains the exact ordered premise; weak conclusions
    /// may also consume a strict premise.
    NegateOrder,
    AddNonnegative,
    AddPositive,
    AddPositiveLeftStrict,
    AddPositiveRightStrict,
    MulNonnegative,
    MulPositive,
    DivNonnegative,
    DivPositive,
    AddCommonLeftLessEqual,
    SubRightNonnegativeLessEqual,
    AddRightNonnegativeLessEqual,
    AddComponentwiseLessEqual,
    /// If `0 <= a`, `0 <= b`, `a <= c`, and `b <= d`, then
    /// `a * b <= c * d` in the checked real carrier.
    MulComponentwiseLessEqual,
    MulCommonFactorLessEqualNonnegative,
    MulCommonFactorLessEqualNonpositive,
    MulCommonFactorLessPositive,
    MulCommonFactorLessNegative,
    AddCommonLeftLess,
    AddComponentwiseLess,
    AddComponentwiseLessLessEqual,
    AddComponentwiseLessEqualLess,
    /// If `a <= b` and `c < d`, then `a - d < b - c` in the
    /// checked real carrier.
    SubComponentwiseLessEqualLess,
    /// If `a <= b` and `c <= d`, then `a - d <= b - c` in the
    /// checked real carrier.
    SubComponentwiseLessEqual,
}

impl ArithmeticBuiltinRule {
    pub fn rule_id(self) -> &'static str {
        match self {
            Self::OrderTransitivity => "order.transitivity",
            Self::LessEqualFromStrictOrder => "order.less_equal_of_less",
            Self::GreaterEqualFromStrictOrder => "order.greater_equal_of_greater",
            Self::SubNonnegativeFromLessEqual => "order.sub_nonnegative_of_less_equal",
            Self::SubPositiveFromLess => "order.sub_positive_of_less",
            Self::SubLessImpliesLessAdd => "order.lt_add_of_sub_lt",
            Self::SubLessSwap => "order.sub_lt_swap",
            Self::SubLessEqualSwap => "order.sub_le_swap",
            Self::LessEqualAddImpliesSubLessEqual => "order.sub_le_of_le_add",
            Self::NegateOrder => "order.negate",
            Self::AddNonnegative => "order.add_nonnegative",
            Self::AddPositive => "order.add_positive",
            Self::AddPositiveLeftStrict => "order.add_positive_of_positive_nonnegative",
            Self::AddPositiveRightStrict => "order.add_positive_of_nonnegative_positive",
            Self::MulNonnegative => "order.mul_nonnegative",
            Self::MulPositive => "order.mul_positive",
            Self::DivNonnegative => "order.div_nonnegative",
            Self::DivPositive => "order.div_positive",
            Self::AddCommonLeftLessEqual => "order.add_le_add_left",
            Self::SubRightNonnegativeLessEqual => "order.sub_le_of_le_of_nonnegative",
            Self::AddRightNonnegativeLessEqual => "order.le_add_of_nonnegative_right",
            Self::AddComponentwiseLessEqual => "order.add_le_add",
            Self::MulComponentwiseLessEqual => "order.mul_le_mul_nonnegative",
            Self::MulCommonFactorLessEqualNonnegative => {
                "order.mul_le_mul_of_nonnegative_common_factor"
            }
            Self::MulCommonFactorLessEqualNonpositive => {
                "order.mul_le_mul_of_nonpositive_common_factor"
            }
            Self::MulCommonFactorLessPositive => "order.mul_lt_mul_of_positive_common_factor",
            Self::MulCommonFactorLessNegative => "order.mul_lt_mul_of_negative_common_factor",
            Self::AddCommonLeftLess => "order.add_lt_add_left",
            Self::AddComponentwiseLess => "order.add_lt_add",
            Self::AddComponentwiseLessLessEqual => "order.add_lt_add_of_lt_of_le",
            Self::AddComponentwiseLessEqualLess => "order.add_lt_add_of_le_of_lt",
            Self::SubComponentwiseLessEqualLess => "order.sub_lt_sub_of_le_of_lt",
            Self::SubComponentwiseLessEqual => "order.sub_le_sub",
        }
    }
}
