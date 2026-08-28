//! Absolute-value, extrema, aggregate, and nonzero builtin rules.

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AbsoluteValueBuiltinRule {
    Nonnegative,
    SelfLessEqual,
    NegationLessEqual,
    NegativeAbsoluteLessEqual,
    TriangleAdd,
    TriangleSub,
    ReverseTriangleAdd,
    ReverseTriangleSub,
    NonnegativeIdentity,
    NonpositiveNegation,
    Product,
    PositiveFromNonzero,
}

impl AbsoluteValueBuiltinRule {
    pub fn rule_id(self) -> &'static str {
        match self {
            Self::Nonnegative => "order.abs_nonnegative",
            Self::SelfLessEqual => "order.self_le_abs",
            Self::NegationLessEqual => "order.neg_le_abs",
            Self::NegativeAbsoluteLessEqual => "order.neg_abs_le",
            Self::TriangleAdd => "order.abs_add_le",
            Self::TriangleSub => "order.abs_sub_le_sum",
            Self::ReverseTriangleAdd => "order.abs_sub_abs_le_abs_add",
            Self::ReverseTriangleSub => "order.abs_sub_abs_le_abs_sub",
            Self::NonnegativeIdentity => "order.abs_eq_self_of_nonnegative",
            Self::NonpositiveNegation => "order.abs_eq_neg_of_nonpositive",
            Self::Product => "algebra.abs_mul",
            Self::PositiveFromNonzero => "order.abs_positive_of_nonzero",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ExtremaBuiltinRule {
    MinLessEqualLeft,
    MinLessEqualRight,
    LessEqualMaxLeft,
    LessEqualMaxRight,
    MinEqLeftOfLessEqual,
    MinEqRightOfLessEqual,
    MaxEqLeftOfLessEqual,
    MaxEqRightOfLessEqual,
    MinCommutative,
    MinAssociative,
    MinIdempotent,
    MinAbsorbMaxLeft,
    MaxCommutative,
    MaxAssociative,
    MaxIdempotent,
    MaxAbsorbMinLeft,
    MinMonotone,
    MaxMonotone,
}

impl ExtremaBuiltinRule {
    pub fn rule_id(self) -> &'static str {
        match self {
            Self::MinLessEqualLeft => "order.min_le_left",
            Self::MinLessEqualRight => "order.min_le_right",
            Self::LessEqualMaxLeft => "order.le_max_left",
            Self::LessEqualMaxRight => "order.le_max_right",
            Self::MinEqLeftOfLessEqual => "order.min_eq_left_of_le",
            Self::MinEqRightOfLessEqual => "order.min_eq_right_of_le",
            Self::MaxEqLeftOfLessEqual => "order.max_eq_left_of_le",
            Self::MaxEqRightOfLessEqual => "order.max_eq_right_of_le",
            Self::MinCommutative => "order.min_commutative",
            Self::MinAssociative => "order.min_associative",
            Self::MinIdempotent => "order.min_idempotent",
            Self::MinAbsorbMaxLeft => "order.min_absorb_max_left",
            Self::MaxCommutative => "order.max_commutative",
            Self::MaxAssociative => "order.max_associative",
            Self::MaxIdempotent => "order.max_idempotent",
            Self::MaxAbsorbMinLeft => "order.max_absorb_min_left",
            Self::MinMonotone => "order.min_monotone",
            Self::MaxMonotone => "order.max_monotone",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AggregateBuiltinRule {
    SumSingle,
    SumSplitLast,
}

impl AggregateBuiltinRule {
    pub fn rule_id(self) -> &'static str {
        match self {
            Self::SumSingle => "aggregate.sum_single",
            Self::SumSplitLast => "aggregate.sum_split_last",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NonzeroBuiltinRule {
    Mul,
}

impl NonzeroBuiltinRule {
    pub fn rule_id(self) -> &'static str {
        match self {
            Self::Mul => "nonzero.mul",
        }
    }
}
