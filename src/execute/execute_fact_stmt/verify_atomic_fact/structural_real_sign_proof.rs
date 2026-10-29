//! Real sign certificates; every branch implies real membership as well as its sign.
use crate::prelude::*;

pub struct StructuralRealSignProof {
    pub element: Obj,
    pub sign: RealSign,
    pub reason: StructuralRealSignReason,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RealSign {
    Positive,
    Negative,
    Nonnegative,
    Nonpositive,
    Nonzero,
    Zero,
}

pub enum StructuralRealSignReason {
    Known {
        real: Box<StructuralMembershipProof>,
        source: Box<AtomicExceptEqualityFactKnownProof>,
    },
    WeakAndNonzero {
        real: Box<StructuralMembershipProof>,
        weak: Box<AtomicExceptEqualityFactKnownProof>,
        nonzero: Box<AtomicExceptEqualityFactKnownProof>,
    },
    WeakSignAndNonzero {
        weak: Box<StructuralRealSignProof>,
        nonzero: Box<StructuralRealSignProof>,
    },
    Membership(Box<StructuralMembershipProof>),
    Closed(Box<ClosedAtomicExceptEqualityCalculationProof>),
    ZeroLiteral,
    Neg {
        argument: Box<StructuralRealSignProof>,
    },
    Add {
        left: Box<StructuralRealSignProof>,
        right: Box<StructuralRealSignProof>,
    },
    Sub {
        left: Box<StructuralRealSignProof>,
        right: Box<StructuralRealSignProof>,
    },
    Mul {
        left: Box<StructuralRealSignProof>,
        right: Box<StructuralRealSignProof>,
    },
    Div {
        left: Box<StructuralRealSignProof>,
        right: Box<StructuralRealSignProof>,
    },
    MinBoth {
        left: Box<StructuralRealSignProof>,
        right: Box<StructuralRealSignProof>,
    },
    MaxBoth {
        left: Box<StructuralRealSignProof>,
        right: Box<StructuralRealSignProof>,
    },
    MinLeft {
        selected: Box<StructuralRealSignProof>,
        other_real: Box<StructuralMembershipProof>,
    },
    MinRight {
        selected: Box<StructuralRealSignProof>,
        other_real: Box<StructuralMembershipProof>,
    },
    MaxLeft {
        selected: Box<StructuralRealSignProof>,
        other_real: Box<StructuralMembershipProof>,
    },
    MaxRight {
        selected: Box<StructuralRealSignProof>,
        other_real: Box<StructuralMembershipProof>,
    },
    PositivePower {
        base: Box<StructuralRealSignProof>,
        exponent_real: Box<StructuralMembershipProof>,
    },
    PositiveEvenPower {
        base: Box<StructuralRealSignProof>,
        exponent: Obj,
    },
    NonnegativeEvenPower {
        base_real: Box<StructuralMembershipProof>,
        exponent: Obj,
    },
    PositiveAbs {
        argument: Box<StructuralRealSignProof>,
    },
    NonnegativeAbs {
        argument_real: Box<StructuralMembershipProof>,
    },
    PositiveSqrt {
        argument: Box<StructuralRealSignProof>,
    },
    NonnegativeSqrt {
        argument_real: Box<StructuralMembershipProof>,
    },
}

pub struct SignedNumericMembershipProof {
    pub base_membership: StructuralMembershipProof,
    pub sign: StructuralRealSignProof,
}

impl StructuralRealSignProof {
    pub fn new(element: Obj, sign: RealSign, reason: StructuralRealSignReason) -> Self {
        Self {
            element,
            sign,
            reason,
        }
    }
}
impl SignedNumericMembershipProof {
    pub fn new(base_membership: StructuralMembershipProof, sign: StructuralRealSignProof) -> Self {
        Self {
            base_membership,
            sign,
        }
    }
}
impl RealSign {
    pub fn implies(self, wanted: Self) -> bool {
        self == wanted
            || match wanted {
                Self::Nonnegative => matches!(self, Self::Positive | Self::Zero),
                Self::Nonpositive => matches!(self, Self::Negative | Self::Zero),
                Self::Nonzero => matches!(self, Self::Positive | Self::Negative),
                _ => false,
            }
    }
    pub fn negated(self) -> Self {
        match self {
            Self::Positive => Self::Negative,
            Self::Negative => Self::Positive,
            Self::Nonnegative => Self::Nonpositive,
            Self::Nonpositive => Self::Nonnegative,
            other => other,
        }
    }
}
