use crate::prelude::*;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PositiveStandardSetMembershipImpliesPositiveInferRule {
    pub source_set: StandardSet,
}

/// A checked equality transports the closed positive-real membership of one
/// literal polynomial power to its opposite endpoint.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ClosedPositivePowerEqualityImpliesEqualSideMembershipInferRule {
    pub power_is_left_endpoint: bool,
}

/// A checked equality transports `R+` membership from a positive integer base
/// raised to a closed natural exponent to the opposite equality endpoint. The
/// application additionally cites the exact base-positivity and `Z` premises.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PositiveIntegerBaseNaturalPowerEqualityImpliesEqualSideMembershipInferRule {
    pub power_is_left_endpoint: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NegativeStandardSetMembershipImpliesNegativeInferRule {
    pub source_set: StandardSet,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NonzeroStandardSetMembershipImpliesNonzeroInferRule {
    pub source_set: StandardSet,
}
