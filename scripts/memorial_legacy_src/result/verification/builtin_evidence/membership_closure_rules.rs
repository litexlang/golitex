//! Numeric-carrier membership closure rules.

/// Stable identities for closure of the integer carrier under binary
/// arithmetic. The enclosing result contains the checked left- and
/// right-operand memberships in that exact order.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum IntegerMembershipClosureBuiltinRule {
    Add,
    Sub,
    Mul,
    Mod,
    /// Integer base raised to a checked natural exponent.
    PowNat,
}

impl IntegerMembershipClosureBuiltinRule {
    pub fn rule_id(self) -> &'static str {
        match self {
            Self::Add => "numeric.integer.add_membership",
            Self::Sub => "numeric.integer.sub_membership",
            Self::Mul => "numeric.integer.mul_membership",
            Self::Mod => "numeric.integer.mod_membership",
            Self::PowNat => "numeric.integer.pow_nat_membership",
        }
    }
}

/// Stable identities for closure of the natural carrier under binary
/// arithmetic. The enclosing result contains the checked left- and
/// right-operand memberships in that exact order.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NaturalMembershipClosureBuiltinRule {
    Add,
    Mul,
}

impl NaturalMembershipClosureBuiltinRule {
    pub fn rule_id(self) -> &'static str {
        match self {
            Self::Add => "numeric.natural.add_membership",
            Self::Mul => "numeric.natural.mul_membership",
        }
    }
}

/// Stable identities for closure of the positive-natural carrier. Addition
/// stays positive when either ordered operand is positive and the other is a
/// natural; multiplication requires both ordered operands to be positive.
/// The enclosing result retains those membership premises in source order.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PositiveNaturalMembershipClosureBuiltinRule {
    AddBothPositive,
    AddLeftPositive,
    AddRightPositive,
    MulBothPositive,
}

impl PositiveNaturalMembershipClosureBuiltinRule {
    pub fn rule_id(self) -> &'static str {
        match self {
            Self::AddBothPositive => "numeric.positive_natural.add_both_positive_membership",
            Self::AddLeftPositive => "numeric.positive_natural.add_left_positive_membership",
            Self::AddRightPositive => "numeric.positive_natural.add_right_positive_membership",
            Self::MulBothPositive => "numeric.positive_natural.mul_membership",
        }
    }
}

/// Stable identities for closure of the rational carrier under binary
/// arithmetic. The enclosing result contains the checked left- and
/// right-operand memberships in that exact order.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RationalMembershipClosureBuiltinRule {
    Add,
    Sub,
    Mul,
    Div,
    Pow,
}

impl RationalMembershipClosureBuiltinRule {
    pub fn rule_id(self) -> &'static str {
        match self {
            Self::Add => "numeric.rational.add_membership",
            Self::Sub => "numeric.rational.sub_membership",
            Self::Mul => "numeric.rational.mul_membership",
            Self::Div => "numeric.rational.div_membership",
            Self::Pow => "numeric.rational.pow_membership",
        }
    }
}

/// Stable identities for closure of the complex carrier under the migrated
/// proof-carrying binary arithmetic constructors.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ComplexArithmeticMembershipClosureBuiltinRule {
    Add,
    Sub,
    Mul,
    Div,
}

impl ComplexArithmeticMembershipClosureBuiltinRule {
    pub fn rule_id(self) -> &'static str {
        match self {
            Self::Add => "numeric.complex.add_membership",
            Self::Sub => "numeric.complex.sub_membership",
            Self::Mul => "numeric.complex.mul_membership",
            Self::Div => "numeric.complex.div_membership",
        }
    }
}

/// Stable identities for closure of the real carrier under arithmetic. The
/// enclosing result retains the checked operand memberships in source order.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RealArithmeticMembershipClosureBuiltinRule {
    Add,
    Sub,
    Mul,
    Div,
    Pow,
    Abs,
}

impl RealArithmeticMembershipClosureBuiltinRule {
    pub fn rule_id(self) -> &'static str {
        match self {
            Self::Add => "numeric.real.add_membership",
            Self::Sub => "numeric.real.sub_membership",
            Self::Mul => "numeric.real.mul_membership",
            Self::Div => "numeric.real.div_membership",
            Self::Pow => "numeric.real.pow_membership",
            Self::Abs => "numeric.real.abs_membership",
        }
    }
}

/// Stable identities for primitive mathematical-constant memberships that
/// need no premises.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NativeConstantMembershipBuiltinRule {
    ImaginaryUnitInComplex,
    EulerNumberInReal,
    PiInReal,
    EulerNumberInPositiveReal,
    PiInPositiveReal,
    EulerNumberInComplex,
    PiInComplex,
}

impl NativeConstantMembershipBuiltinRule {
    pub fn rule_id(self) -> &'static str {
        match self {
            Self::ImaginaryUnitInComplex => "numeric.constant.i_in_complex",
            Self::EulerNumberInReal => "numeric.constant.e_in_real",
            Self::PiInReal => "numeric.constant.pi_in_real",
            Self::EulerNumberInPositiveReal => "numeric.constant.e_in_positive_real",
            Self::PiInPositiveReal => "numeric.constant.pi_in_positive_real",
            Self::EulerNumberInComplex => "numeric.constant.e_in_complex",
            Self::PiInComplex => "numeric.constant.pi_in_complex",
        }
    }
}
