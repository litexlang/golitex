use crate::ast::obj::{Obj, StandardSet};
use crate::rational_expression::exact_rational::EvalRational;
use crate::rational_expression::NumberCompareResult;

// Success evidence only. Unsupported expressions and false goals yield None at
// the calculator boundary, never a successful proof with a failure flag.
pub enum ClosedCalculationProof {
    Equality(ClosedEqualityCalculationProof),
    AtomicExceptEquality(ClosedAtomicExceptEqualityCalculationProof),
}

pub struct ClosedEqualityCalculationProof {
    pub values: ClosedValuePair,
}

pub enum ClosedAtomicExceptEqualityCalculationProof {
    NotEqual(ClosedNotEqualCalculationProof),
    Less(ClosedComparisonCalculationProof),
    Greater(ClosedComparisonCalculationProof),
    LessEqual(ClosedComparisonCalculationProof),
    GreaterEqual(ClosedComparisonCalculationProof),
    NotLess(ClosedComparisonCalculationProof),
    NotGreater(ClosedComparisonCalculationProof),
    NotLessEqual(ClosedComparisonCalculationProof),
    NotGreaterEqual(ClosedComparisonCalculationProof),
    In(ClosedMembershipCalculationProof),
    NotIn(ClosedMembershipCalculationProof),
}

// Both values use the same exact representation. Decimal strings are normalized;
// rational/complex arithmetic uses checked exact fractions, never floats.
pub enum ClosedValuePair {
    Radical {
        left_normal: Obj,
        right_normal: Obj,
    },
    Decimal {
        left: String,
        right: String,
    },
    Rational {
        left: EvalRational,
        right: EvalRational,
    },
    Complex {
        left_real: EvalRational,
        left_imaginary: EvalRational,
        right_real: EvalRational,
        right_imaginary: EvalRational,
    },
}

pub struct ClosedNotEqualCalculationProof {
    pub values: ClosedValuePair,
}

pub struct ClosedComparisonCalculationProof {
    pub left_normal: String,
    pub right_normal: String,
    pub comparison: NumberCompareResult,
}

pub enum ClosedScalarValue {
    Decimal(String),
    ExactComplex {
        real: EvalRational,
        imaginary: EvalRational,
    },
}

pub enum ClosedMembershipCalculationProof {
    StandardSet {
        value: ClosedScalarValue,
        set: StandardSet,
    },
    IntegerRange {
        value: ClosedScalarValue,
        set: Obj,
        start: ClosedScalarValue,
        end: ClosedScalarValue,
    },
}
