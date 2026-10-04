use super::closed_calculation_proof::ClosedMembershipCalculationProof;
use super::AtomicExceptEqualityFactSearchProofByKnownAtomicFact;
use crate::ast::obj::{Obj, StandardSet};

// Success-only tree. Constructor rules use the enclosing fact's object WD;
// division and integer powers therefore retain their domain guards in that WD.
pub struct StructuralMembershipProof {
    pub element: Obj,
    pub set: StandardSet,
    pub reason: StructuralMembershipReason,
}

pub enum StructuralMembershipReason {
    Known(AtomicExceptEqualityFactSearchProofByKnownAtomicFact),
    Closed(ClosedMembershipCalculationProof),
    StandardSuperset(Box<StructuralMembershipProof>),
    Add {
        left: Box<StructuralMembershipProof>,
        right: Box<StructuralMembershipProof>,
    },
    Sub {
        left: Box<StructuralMembershipProof>,
        right: Box<StructuralMembershipProof>,
    },
    Mul {
        left: Box<StructuralMembershipProof>,
        right: Box<StructuralMembershipProof>,
    },
    Div {
        left: Box<StructuralMembershipProof>,
        right: Box<StructuralMembershipProof>,
    },
    Neg {
        argument: Box<StructuralMembershipProof>,
    },
    Abs {
        argument: Box<StructuralMembershipProof>,
    },
    Pow {
        base: Box<StructuralMembershipProof>,
        exponent: Box<StructuralMembershipProof>,
    },
    Intrinsic(IntrinsicCodomain),
}

// Fixed output types only, after object WD. These do not evaluate the value,
// select user-function signatures, or prove any missing input-domain condition.
pub enum IntrinsicCodomain {
    Floor,
    Ceil,
    Sign,
    Min,
    Max,
    Mod,
    Quot,
    Gcd,
    Lcm,
    Factorial,
    Exp,
    Abs,
    Sqrt,
    Log,
    Ln,
    Sin,
    Cos,
    Tan,
    Cot,
    Arcsin,
    Arccos,
    Arctan,
    Arccot,
    RealPart,
    ImaginaryPart,
    ComplexAbs,
    TupleDim,
    CartDim,
    FiniteSetSize,
    EulerNumber,
    Pi,
    ImaginaryUnit,
}

impl StructuralMembershipProof {
    pub fn new(element: Obj, set: StandardSet, reason: StructuralMembershipReason) -> Self {
        Self {
            element,
            set,
            reason,
        }
    }
}
