use super::closed_calculation_proof::ClosedMembershipCalculationProof;
use super::verify_atomic_except_equality::result::AtomicExceptEqualityFactKnownProof;
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
    KnownSubset(KnownSubsetMembershipProof),
    StandardSuperset(Box<StructuralMembershipProof>),
    Add {
        left: Box<StructuralMembershipProof>,
        right: Box<StructuralMembershipProof>,
    },
    Sub {
        left: Box<StructuralMembershipProof>,
        right: Box<StructuralMembershipProof>,
    },
    Min {
        left: Box<StructuralMembershipProof>,
        right: Box<StructuralMembershipProof>,
    },
    Max {
        left: Box<StructuralMembershipProof>,
        right: Box<StructuralMembershipProof>,
    },
    // max(a,b)-a and max(a,b)-b are natural for natural a,b.
    // The selected operand is syntactically the actual subtrahend.
    NaturalMaxDifference {
        maximum: Box<StructuralMembershipProof>,
        subtrahend: Box<StructuralMembershipProof>,
        right_operand: bool,
    },
    Mul {
        left: Box<StructuralMembershipProof>,
        right: Box<StructuralMembershipProof>,
    },
    Div {
        left: Box<StructuralMembershipProof>,
        right: Box<StructuralMembershipProof>,
    },
    ExactIntegerDiv {
        numerator: Box<StructuralMembershipProof>,
        denominator: Box<StructuralMembershipProof>,
        divisibility: Box<AtomicExceptEqualityFactKnownProof>,
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
    MatrixDeterminant,
    MatrixTrace,
    MatrixRank,
    MatrixCofactor,
    FiniteInnerProduct,
    EuclideanNorm,
    MatrixFrobeniusNorm,
    RiemannIntegral,
    DerivativeAt,
    SequenceLimit,
    SequenceLimsup,
    Supremum,
    Infimum,
    SequenceLiminf,
    FunctionLimit,
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
    Sec,
    Csc,
    Conjugate,
    Sinh,
    Cosh,
    Tanh,
    Coth,
    Sech,
    Csch,

    Arcsin,
    Arccos,
    Arctan,
    Arccot,
    RealPart,
    ImaginaryPart,
    ComplexAbs,

    FiniteSetSize,
    FiniteSetMax,
    FiniteSetMin,
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

// Both complete atomic premise citations are retained for replay and output.
pub struct KnownSubsetMembershipProof {
    pub member_proof:
        super::verify_atomic_except_equality::result::AtomicExceptEqualityFactKnownProof,
    pub subset_proof:
        super::verify_atomic_except_equality::result::AtomicExceptEqualityFactKnownProof,
}

impl KnownSubsetMembershipProof {
    pub fn new(
        member_proof: super::verify_atomic_except_equality::result::AtomicExceptEqualityFactKnownProof,
        subset_proof: super::verify_atomic_except_equality::result::AtomicExceptEqualityFactKnownProof,
    ) -> Self {
        Self {
            member_proof,
            subset_proof,
        }
    }
}
