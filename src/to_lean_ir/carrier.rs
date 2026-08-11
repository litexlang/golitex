use crate::symbol::SymbolId;

use super::{FunctionTypeToLeanIR, ObjToLeanIR, StandardSetToLeanIR};

/// A checked target carrier constraint attached to a binder or fact boundary.
///
/// Object identity remains in `ObjToLeanIR`. This enum records only the Lean
/// type in which that object must elaborate. `Generic` names a fresh carrier
/// by a stable source binding; `ElementOfSet` defers the carrier to a checked
/// set expression without inventing a universal object wrapper.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LeanCarrierToLeanIR {
    Natural,
    Integer,
    Rational,
    Real,
    Complex,
    Generic {
        anchor: SymbolId,
    },
    Set {
        element_carrier: Box<LeanCarrierToLeanIR>,
    },
    Function {
        function: Box<FunctionTypeToLeanIR>,
    },
    ElementOfSet {
        set: Box<ObjToLeanIR>,
    },
}

impl LeanCarrierToLeanIR {
    pub fn for_membership_set(set: &ObjToLeanIR) -> Self {
        match set {
            ObjToLeanIR::StandardSet(standard) => standard.element_carrier(),
            ObjToLeanIR::FunctionSet { function } => LeanCarrierToLeanIR::Function {
                function: function.clone(),
            },
            _ => LeanCarrierToLeanIR::ElementOfSet {
                set: Box::new(set.clone()),
            },
        }
    }
}

impl StandardSetToLeanIR {
    pub fn element_carrier(self) -> LeanCarrierToLeanIR {
        match self {
            StandardSetToLeanIR::PositiveNatural | StandardSetToLeanIR::Natural => {
                LeanCarrierToLeanIR::Natural
            }
            StandardSetToLeanIR::Integer
            | StandardSetToLeanIR::NegativeInteger
            | StandardSetToLeanIR::NonzeroInteger => LeanCarrierToLeanIR::Integer,
            StandardSetToLeanIR::Rational
            | StandardSetToLeanIR::PositiveRational
            | StandardSetToLeanIR::NegativeRational
            | StandardSetToLeanIR::NonzeroRational => LeanCarrierToLeanIR::Rational,
            StandardSetToLeanIR::Real
            | StandardSetToLeanIR::PositiveReal
            | StandardSetToLeanIR::NegativeReal
            | StandardSetToLeanIR::NonzeroReal => LeanCarrierToLeanIR::Real,
            StandardSetToLeanIR::Complex | StandardSetToLeanIR::NonzeroComplex => {
                LeanCarrierToLeanIR::Complex
            }
        }
    }
}
