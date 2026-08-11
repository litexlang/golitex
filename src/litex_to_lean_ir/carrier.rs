use crate::symbol::SymbolId;

use super::{LitexToLeanFunctionTypeIr, LitexToLeanObjectIr, LitexToLeanStandardSetIr};

/// A checked target carrier constraint attached to a binder or fact boundary.
///
/// Object identity remains in `LitexToLeanObjectIr`. This enum records only the Lean
/// type in which that object must elaborate. `Generic` names a fresh carrier
/// by a stable source binding; `ElementOfSet` defers the carrier to a checked
/// set expression without inventing a universal object wrapper.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LitexToLeanCarrierIr {
    Natural,
    Integer,
    Rational,
    Real,
    Complex,
    Generic {
        anchor: SymbolId,
    },
    Set {
        element_carrier: Box<LitexToLeanCarrierIr>,
    },
    Function {
        function: Box<LitexToLeanFunctionTypeIr>,
    },
    ElementOfSet {
        set: Box<LitexToLeanObjectIr>,
    },
}

impl LitexToLeanCarrierIr {
    pub fn for_membership_set(set: &LitexToLeanObjectIr) -> Self {
        match set {
            LitexToLeanObjectIr::StandardSet(standard) => standard.element_carrier(),
            LitexToLeanObjectIr::FunctionSet { function } => LitexToLeanCarrierIr::Function {
                function: function.clone(),
            },
            _ => LitexToLeanCarrierIr::ElementOfSet {
                set: Box::new(set.clone()),
            },
        }
    }
}

impl LitexToLeanStandardSetIr {
    pub fn element_carrier(self) -> LitexToLeanCarrierIr {
        match self {
            LitexToLeanStandardSetIr::PositiveNatural | LitexToLeanStandardSetIr::Natural => {
                LitexToLeanCarrierIr::Natural
            }
            LitexToLeanStandardSetIr::Integer
            | LitexToLeanStandardSetIr::NegativeInteger
            | LitexToLeanStandardSetIr::NonzeroInteger => LitexToLeanCarrierIr::Integer,
            LitexToLeanStandardSetIr::Rational
            | LitexToLeanStandardSetIr::PositiveRational
            | LitexToLeanStandardSetIr::NegativeRational
            | LitexToLeanStandardSetIr::NonzeroRational => LitexToLeanCarrierIr::Rational,
            LitexToLeanStandardSetIr::Real
            | LitexToLeanStandardSetIr::PositiveReal
            | LitexToLeanStandardSetIr::NegativeReal
            | LitexToLeanStandardSetIr::NonzeroReal => LitexToLeanCarrierIr::Real,
            LitexToLeanStandardSetIr::Complex | LitexToLeanStandardSetIr::NonzeroComplex => {
                LitexToLeanCarrierIr::Complex
            }
        }
    }
}
