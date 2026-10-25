use super::super::line_file::SourceLine;
use super::super::names::AtomicName;
use super::super::obj::Obj;
use crate::runtime::FactId;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AtomicFact {
    MultivariableAnalysisFact(MultivariableAnalysisFact),
    NotMultivariableAnalysisFact(NotMultivariableAnalysisFact),
    HasRiemannIntegralFact(HasRiemannIntegralFact),
    NotHasRiemannIntegralFact(NotHasRiemannIntegralFact),
    FunctionRiemannIntegrableFact(FunctionRiemannIntegrableFact),
    NotFunctionRiemannIntegrableFact(NotFunctionRiemannIntegrableFact),
    HasDerivativeAtFact(HasDerivativeAtFact),
    NotHasDerivativeAtFact(NotHasDerivativeAtFact),
    FunctionDifferentiableAtFact(FunctionDifferentiableAtFact),
    NotFunctionDifferentiableAtFact(NotFunctionDifferentiableAtFact),

    RealSetBoundFact(RealSetBoundFact),
    NotRealSetBoundFact(NotRealSetBoundFact),
    RealSetBoundedFact(RealSetBoundedFact),
    NotRealSetBoundedFact(NotRealSetBoundedFact),
    SequenceAnalysisFact(SequenceAnalysisFact),
    NotSequenceAnalysisFact(NotSequenceAnalysisFact),
    RealAccumulationFact(RealAccumulationFact),
    NotRealAccumulationFact(NotRealAccumulationFact),
    FunctionContinuousAtFact(FunctionContinuousAtFact),
    NotFunctionContinuousAtFact(NotFunctionContinuousAtFact),
    FunctionContinuousFact(FunctionContinuousFact),
    NotFunctionContinuousFact(NotFunctionContinuousFact),
    FunctionLipschitzFact(FunctionLipschitzFact),
    NotFunctionLipschitzFact(NotFunctionLipschitzFact),
    HasFunctionLimitFact(HasFunctionLimitFact),
    NotHasFunctionLimitFact(NotHasFunctionLimitFact),
    HasSequenceLimitFact(HasSequenceLimitFact),
    HasSequenceLimsupFact(HasSequenceLimsupFact),
    HasSequenceLiminfFact(HasSequenceLiminfFact),
    NotHasSequenceLimitFact(NotHasSequenceLimitFact),
    NotHasSequenceLimsupFact(NotHasSequenceLimsupFact),
    NotHasSequenceLiminfFact(NotHasSequenceLiminfFact),
    // User-defined `$prop(...)` only. Official builtins have dedicated variants.
    NormalAtomicFact(NormalAtomicFact),
    EqualFact(EqualFact),
    LessFact(LessFact),
    GreaterFact(GreaterFact),
    LessEqualFact(LessEqualFact),
    GreaterEqualFact(GreaterEqualFact),
    IsSetFact(IsSetFact),
    IsNonemptySetFact(IsNonemptySetFact),
    IsFiniteSetFact(IsFiniteSetFact),
    InFact(InFact),

    SubsetFact(SubsetFact),
    SupersetFact(SupersetFact),
    ProperSubsetFact(ProperSubsetFact),
    ProperSupersetFact(ProperSupersetFact),
    PrimeFact(PrimeFact),
    CoprimeFact(CoprimeFact),
    DvdFact(DvdFact),
    InjectiveFact(InjectiveFact),
    SurjectiveFact(SurjectiveFact),
    BijectiveFact(BijectiveFact),
    IsChoiceFunctionForFact(IsChoiceFunctionForFact),
    NotNormalAtomicFact(NotNormalAtomicFact),
    NotEqualFact(NotEqualFact),
    NotLessFact(NotLessFact),
    NotGreaterFact(NotGreaterFact),
    NotLessEqualFact(NotLessEqualFact),
    NotGreaterEqualFact(NotGreaterEqualFact),
    NotIsSetFact(NotIsSetFact),
    NotIsNonemptySetFact(NotIsNonemptySetFact),
    NotIsFiniteSetFact(NotIsFiniteSetFact),
    NotInFact(NotInFact),

    NotSubsetFact(NotSubsetFact),
    NotSupersetFact(NotSupersetFact),
    NotProperSubsetFact(NotProperSubsetFact),
    NotProperSupersetFact(NotProperSupersetFact),
    NotPrimeFact(NotPrimeFact),
    NotCoprimeFact(NotCoprimeFact),
    NotDvdFact(NotDvdFact),
    NotInjectiveFact(NotInjectiveFact),
    NotSurjectiveFact(NotSurjectiveFact),
    NotBijectiveFact(NotBijectiveFact),
    NotIsChoiceFunctionForFact(NotIsChoiceFunctionForFact),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EqualFact {
    pub fact_id: FactId,
    pub left: Obj,
    pub right: Obj,
    pub line_file: Option<SourceLine>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotEqualFact {
    pub fact_id: FactId,
    pub left: Obj,
    pub right: Obj,
    pub line_file: Option<SourceLine>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InFact {
    pub fact_id: FactId,
    pub element: Obj,
    pub set: Obj,
    pub line_file: Option<SourceLine>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotInFact {
    pub fact_id: FactId,
    pub element: Obj,
    pub set: Obj,
    pub line_file: Option<SourceLine>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LessFact {
    pub fact_id: FactId,
    pub left: Obj,
    pub right: Obj,
    pub line_file: Option<SourceLine>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotLessFact {
    pub fact_id: FactId,
    pub left: Obj,
    pub right: Obj,
    pub line_file: Option<SourceLine>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GreaterFact {
    pub fact_id: FactId,
    pub left: Obj,
    pub right: Obj,
    pub line_file: Option<SourceLine>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotGreaterFact {
    pub fact_id: FactId,
    pub left: Obj,
    pub right: Obj,
    pub line_file: Option<SourceLine>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LessEqualFact {
    pub fact_id: FactId,
    pub left: Obj,
    pub right: Obj,
    pub line_file: Option<SourceLine>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotLessEqualFact {
    pub fact_id: FactId,
    pub left: Obj,
    pub right: Obj,
    pub line_file: Option<SourceLine>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GreaterEqualFact {
    pub fact_id: FactId,
    pub left: Obj,
    pub right: Obj,
    pub line_file: Option<SourceLine>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotGreaterEqualFact {
    pub fact_id: FactId,
    pub left: Obj,
    pub right: Obj,
    pub line_file: Option<SourceLine>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NormalAtomicFact {
    pub fact_id: FactId,
    pub predicate: AtomicName,
    pub body: Vec<Obj>,
    pub line_file: Option<SourceLine>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotNormalAtomicFact {
    pub fact_id: FactId,
    pub predicate: AtomicName,
    pub body: Vec<Obj>,
    pub line_file: Option<SourceLine>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IsSetFact {
    pub fact_id: FactId,
    pub set: Obj,
    pub line_file: Option<SourceLine>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotIsSetFact {
    pub fact_id: FactId,
    pub set: Obj,
    pub line_file: Option<SourceLine>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IsNonemptySetFact {
    pub fact_id: FactId,
    pub set: Obj,
    pub line_file: Option<SourceLine>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotIsNonemptySetFact {
    pub fact_id: FactId,
    pub set: Obj,
    pub line_file: Option<SourceLine>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IsFiniteSetFact {
    pub fact_id: FactId,
    pub set: Obj,
    pub line_file: Option<SourceLine>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotIsFiniteSetFact {
    pub fact_id: FactId,
    pub set: Obj,
    pub line_file: Option<SourceLine>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SupersetFact {
    pub fact_id: FactId,
    pub left: Obj,
    pub right: Obj,
    pub line_file: Option<SourceLine>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotSupersetFact {
    pub fact_id: FactId,
    pub left: Obj,
    pub right: Obj,
    pub line_file: Option<SourceLine>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SubsetFact {
    pub fact_id: FactId,
    pub left: Obj,
    pub right: Obj,
    pub line_file: Option<SourceLine>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotSubsetFact {
    pub fact_id: FactId,
    pub left: Obj,
    pub right: Obj,
    pub line_file: Option<SourceLine>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProperSubsetFact {
    pub fact_id: FactId,
    pub left: Obj,
    pub right: Obj,
    pub line_file: Option<SourceLine>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotProperSubsetFact {
    pub fact_id: FactId,
    pub left: Obj,
    pub right: Obj,
    pub line_file: Option<SourceLine>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProperSupersetFact {
    pub fact_id: FactId,
    pub left: Obj,
    pub right: Obj,
    pub line_file: Option<SourceLine>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotProperSupersetFact {
    pub fact_id: FactId,
    pub left: Obj,
    pub right: Obj,
    pub line_file: Option<SourceLine>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PrimeFact {
    pub fact_id: FactId,
    pub value: Obj,
    pub line_file: Option<SourceLine>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotPrimeFact {
    pub fact_id: FactId,
    pub value: Obj,
    pub line_file: Option<SourceLine>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CoprimeFact {
    pub fact_id: FactId,
    pub left: Obj,
    pub right: Obj,
    pub line_file: Option<SourceLine>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotCoprimeFact {
    pub fact_id: FactId,
    pub left: Obj,
    pub right: Obj,
    pub line_file: Option<SourceLine>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DvdFact {
    pub fact_id: FactId,
    pub left: Obj,
    pub right: Obj,
    pub line_file: Option<SourceLine>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotDvdFact {
    pub fact_id: FactId,
    pub left: Obj,
    pub right: Obj,
    pub line_file: Option<SourceLine>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InjectiveFact {
    pub fact_id: FactId,
    pub domain: Obj,
    pub codomain: Obj,
    pub function: Obj,
    pub line_file: Option<SourceLine>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotInjectiveFact {
    pub fact_id: FactId,
    pub domain: Obj,
    pub codomain: Obj,
    pub function: Obj,
    pub line_file: Option<SourceLine>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SurjectiveFact {
    pub fact_id: FactId,
    pub domain: Obj,
    pub codomain: Obj,
    pub function: Obj,
    pub line_file: Option<SourceLine>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotSurjectiveFact {
    pub fact_id: FactId,
    pub domain: Obj,
    pub codomain: Obj,
    pub function: Obj,
    pub line_file: Option<SourceLine>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BijectiveFact {
    pub fact_id: FactId,
    pub domain: Obj,
    pub codomain: Obj,
    pub function: Obj,
    pub line_file: Option<SourceLine>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotBijectiveFact {
    pub fact_id: FactId,
    pub domain: Obj,
    pub codomain: Obj,
    pub function: Obj,
    pub line_file: Option<SourceLine>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IsChoiceFunctionForFact {
    pub fact_id: FactId,
    pub index: Obj,
    pub set: Obj,
    pub family: Obj,
    pub choice: Obj,
    pub line_file: Option<SourceLine>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotIsChoiceFunctionForFact {
    pub fact_id: FactId,
    pub index: Obj,
    pub set: Obj,
    pub family: Obj,
    pub choice: Obj,
    pub line_file: Option<SourceLine>,
}

impl AtomicFact {
    pub fn fact_id(&self) -> FactId {
        match self {
            AtomicFact::MultivariableAnalysisFact(f) => f.fact_id,
            AtomicFact::NotMultivariableAnalysisFact(f) => f.fact_id,
            AtomicFact::HasRiemannIntegralFact(f) => f.fact_id,
            AtomicFact::NotHasRiemannIntegralFact(f) => f.fact_id,
            AtomicFact::FunctionRiemannIntegrableFact(f) => f.fact_id,
            AtomicFact::NotFunctionRiemannIntegrableFact(f) => f.fact_id,
            AtomicFact::HasDerivativeAtFact(f) => f.fact_id,
            AtomicFact::NotHasDerivativeAtFact(f) => f.fact_id,
            AtomicFact::FunctionDifferentiableAtFact(f) => f.fact_id,
            AtomicFact::NotFunctionDifferentiableAtFact(f) => f.fact_id,
            AtomicFact::RealSetBoundFact(f) => f.fact_id,
            AtomicFact::NotRealSetBoundFact(f) => f.fact_id,
            AtomicFact::RealSetBoundedFact(f) => f.fact_id,
            AtomicFact::NotRealSetBoundedFact(f) => f.fact_id,
            AtomicFact::SequenceAnalysisFact(f) => f.fact_id,
            AtomicFact::NotSequenceAnalysisFact(f) => f.fact_id,
            AtomicFact::RealAccumulationFact(f) => f.fact_id,
            AtomicFact::NotRealAccumulationFact(f) => f.fact_id,
            AtomicFact::FunctionContinuousAtFact(f) => f.fact_id,
            AtomicFact::NotFunctionContinuousAtFact(f) => f.fact_id,
            AtomicFact::FunctionContinuousFact(f) => f.fact_id,
            AtomicFact::NotFunctionContinuousFact(f) => f.fact_id,
            AtomicFact::FunctionLipschitzFact(f) => f.fact_id,
            AtomicFact::NotFunctionLipschitzFact(f) => f.fact_id,
            AtomicFact::HasSequenceLimitFact(f) => f.fact_id,
            AtomicFact::HasSequenceLimsupFact(f) => f.fact_id,
            AtomicFact::HasSequenceLiminfFact(f) => f.fact_id,
            AtomicFact::HasFunctionLimitFact(f) => f.fact_id,
            AtomicFact::NotHasSequenceLimitFact(f) => f.fact_id,
            AtomicFact::NotHasSequenceLimsupFact(f) => f.fact_id,
            AtomicFact::NotHasSequenceLiminfFact(f) => f.fact_id,
            AtomicFact::NotHasFunctionLimitFact(f) => f.fact_id,
            AtomicFact::NormalAtomicFact(f) => f.fact_id,
            AtomicFact::EqualFact(f) => f.fact_id,
            AtomicFact::LessFact(f) => f.fact_id,
            AtomicFact::GreaterFact(f) => f.fact_id,
            AtomicFact::LessEqualFact(f) => f.fact_id,
            AtomicFact::GreaterEqualFact(f) => f.fact_id,
            AtomicFact::IsSetFact(f) => f.fact_id,
            AtomicFact::IsNonemptySetFact(f) => f.fact_id,
            AtomicFact::IsFiniteSetFact(f) => f.fact_id,
            AtomicFact::InFact(f) => f.fact_id,
            AtomicFact::SubsetFact(f) => f.fact_id,
            AtomicFact::SupersetFact(f) => f.fact_id,
            AtomicFact::ProperSubsetFact(f) => f.fact_id,
            AtomicFact::ProperSupersetFact(f) => f.fact_id,
            AtomicFact::PrimeFact(f) => f.fact_id,
            AtomicFact::CoprimeFact(f) => f.fact_id,
            AtomicFact::DvdFact(f) => f.fact_id,
            AtomicFact::InjectiveFact(f) => f.fact_id,
            AtomicFact::SurjectiveFact(f) => f.fact_id,
            AtomicFact::BijectiveFact(f) => f.fact_id,
            AtomicFact::IsChoiceFunctionForFact(f) => f.fact_id,
            AtomicFact::NotNormalAtomicFact(f) => f.fact_id,
            AtomicFact::NotEqualFact(f) => f.fact_id,
            AtomicFact::NotLessFact(f) => f.fact_id,
            AtomicFact::NotGreaterFact(f) => f.fact_id,
            AtomicFact::NotLessEqualFact(f) => f.fact_id,
            AtomicFact::NotGreaterEqualFact(f) => f.fact_id,
            AtomicFact::NotIsSetFact(f) => f.fact_id,
            AtomicFact::NotIsNonemptySetFact(f) => f.fact_id,
            AtomicFact::NotIsFiniteSetFact(f) => f.fact_id,
            AtomicFact::NotInFact(f) => f.fact_id,
            AtomicFact::NotSubsetFact(f) => f.fact_id,
            AtomicFact::NotSupersetFact(f) => f.fact_id,
            AtomicFact::NotProperSubsetFact(f) => f.fact_id,
            AtomicFact::NotProperSupersetFact(f) => f.fact_id,
            AtomicFact::NotPrimeFact(f) => f.fact_id,
            AtomicFact::NotCoprimeFact(f) => f.fact_id,
            AtomicFact::NotDvdFact(f) => f.fact_id,
            AtomicFact::NotInjectiveFact(f) => f.fact_id,
            AtomicFact::NotSurjectiveFact(f) => f.fact_id,
            AtomicFact::NotBijectiveFact(f) => f.fact_id,
            AtomicFact::NotIsChoiceFunctionForFact(f) => f.fact_id,
        }
    }

    // Predicate-family name shared by a fact and its negation (e.g. both use `in`).
    pub fn prop_name(&self) -> AtomicName {
        use crate::parse::keywords::{
            BIJECTIVE, COPRIME, DVD, EQUAL, GREATER, GREATER_EQUAL, IN, INJECTIVE,
            IS_CHOICE_FUNCTION_FOR, IS_FINITE_SET, IS_NONEMPTY_SET, IS_SET, LESS, LESS_EQUAL,
            PRIME, PROPER_SUBSET, PROPER_SUPERSET, SUBSET, SUPERSET, SURJECTIVE,
        };
        match self {
            AtomicFact::MultivariableAnalysisFact(f) => {
                AtomicName::plain(f.relation.predicate_name().into())
            }
            AtomicFact::NotMultivariableAnalysisFact(f) => {
                AtomicName::plain(f.relation.predicate_name().into())
            }
            AtomicFact::HasRiemannIntegralFact(f) => AtomicName::plain(f.predicate_name().into()),
            AtomicFact::NotHasRiemannIntegralFact(f) => {
                AtomicName::plain(f.predicate_name().into())
            }
            AtomicFact::FunctionRiemannIntegrableFact(f) => {
                AtomicName::plain(f.predicate_name().into())
            }
            AtomicFact::NotFunctionRiemannIntegrableFact(f) => {
                AtomicName::plain(f.predicate_name().into())
            }
            AtomicFact::HasDerivativeAtFact(f) => AtomicName::plain(f.predicate_name().into()),
            AtomicFact::NotHasDerivativeAtFact(f) => AtomicName::plain(f.predicate_name().into()),
            AtomicFact::FunctionDifferentiableAtFact(f) => {
                AtomicName::plain(f.predicate_name().into())
            }
            AtomicFact::NotFunctionDifferentiableAtFact(f) => {
                AtomicName::plain(f.predicate_name().into())
            }
            AtomicFact::RealSetBoundFact(f) => AtomicName::plain(f.predicate_name().into()),
            AtomicFact::NotRealSetBoundFact(f) => AtomicName::plain(f.predicate_name().into()),
            AtomicFact::RealSetBoundedFact(f) => AtomicName::plain(f.predicate_name().into()),
            AtomicFact::NotRealSetBoundedFact(f) => AtomicName::plain(f.predicate_name().into()),
            AtomicFact::SequenceAnalysisFact(f) => AtomicName::plain(f.predicate_name().into()),
            AtomicFact::NotSequenceAnalysisFact(f) => AtomicName::plain(f.predicate_name().into()),
            AtomicFact::RealAccumulationFact(f) => AtomicName::plain(f.predicate_name().into()),
            AtomicFact::NotRealAccumulationFact(f) => AtomicName::plain(f.predicate_name().into()),
            AtomicFact::FunctionContinuousAtFact(f) => AtomicName::plain(f.predicate_name().into()),
            AtomicFact::NotFunctionContinuousAtFact(f) => {
                AtomicName::plain(f.predicate_name().into())
            }
            AtomicFact::FunctionContinuousFact(f) => AtomicName::plain(f.predicate_name().into()),
            AtomicFact::NotFunctionContinuousFact(f) => {
                AtomicName::plain(f.predicate_name().into())
            }
            AtomicFact::FunctionLipschitzFact(f) => AtomicName::plain(f.predicate_name().into()),
            AtomicFact::NotFunctionLipschitzFact(f) => AtomicName::plain(f.predicate_name().into()),
            AtomicFact::HasFunctionLimitFact(f) => AtomicName::Plain {
                name: f.approach.predicate_name().into(),
            },
            AtomicFact::NotHasFunctionLimitFact(f) => AtomicName::Plain {
                name: f.approach.predicate_name().into(),
            },
            AtomicFact::HasSequenceLimitFact(_) | AtomicFact::NotHasSequenceLimitFact(_) => {
                AtomicName::Plain {
                    name: "has_seq_limit".into(),
                }
            }
            AtomicFact::HasSequenceLimsupFact(_) | AtomicFact::NotHasSequenceLimsupFact(_) => {
                AtomicName::Plain {
                    name: "has_seq_limsup".into(),
                }
            }
            AtomicFact::HasSequenceLiminfFact(_) | AtomicFact::NotHasSequenceLiminfFact(_) => {
                AtomicName::Plain {
                    name: "has_seq_liminf".into(),
                }
            }
            AtomicFact::NormalAtomicFact(f) => f.predicate.clone(),
            AtomicFact::NotNormalAtomicFact(f) => f.predicate.clone(),
            AtomicFact::EqualFact(_) | AtomicFact::NotEqualFact(_) => {
                AtomicName::Plain { name: EQUAL.into() }
            }
            AtomicFact::LessFact(_) | AtomicFact::NotLessFact(_) => {
                AtomicName::Plain { name: LESS.into() }
            }
            AtomicFact::GreaterFact(_) | AtomicFact::NotGreaterFact(_) => AtomicName::Plain {
                name: GREATER.into(),
            },
            AtomicFact::LessEqualFact(_) | AtomicFact::NotLessEqualFact(_) => AtomicName::Plain {
                name: LESS_EQUAL.into(),
            },
            AtomicFact::GreaterEqualFact(_) | AtomicFact::NotGreaterEqualFact(_) => {
                AtomicName::Plain {
                    name: GREATER_EQUAL.into(),
                }
            }
            AtomicFact::IsSetFact(_) | AtomicFact::NotIsSetFact(_) => AtomicName::Plain {
                name: IS_SET.into(),
            },
            AtomicFact::IsNonemptySetFact(_) | AtomicFact::NotIsNonemptySetFact(_) => {
                AtomicName::Plain {
                    name: IS_NONEMPTY_SET.into(),
                }
            }
            AtomicFact::IsFiniteSetFact(_) | AtomicFact::NotIsFiniteSetFact(_) => {
                AtomicName::Plain {
                    name: IS_FINITE_SET.into(),
                }
            }
            AtomicFact::InFact(_) | AtomicFact::NotInFact(_) => {
                AtomicName::Plain { name: IN.into() }
            }
            AtomicFact::SubsetFact(_) | AtomicFact::NotSubsetFact(_) => AtomicName::Plain {
                name: SUBSET.into(),
            },
            AtomicFact::SupersetFact(_) | AtomicFact::NotSupersetFact(_) => AtomicName::Plain {
                name: SUPERSET.into(),
            },
            AtomicFact::ProperSubsetFact(_) | AtomicFact::NotProperSubsetFact(_) => {
                AtomicName::Plain {
                    name: PROPER_SUBSET.into(),
                }
            }
            AtomicFact::ProperSupersetFact(_) | AtomicFact::NotProperSupersetFact(_) => {
                AtomicName::Plain {
                    name: PROPER_SUPERSET.into(),
                }
            }
            AtomicFact::PrimeFact(_) | AtomicFact::NotPrimeFact(_) => {
                AtomicName::Plain { name: PRIME.into() }
            }
            AtomicFact::CoprimeFact(_) | AtomicFact::NotCoprimeFact(_) => AtomicName::Plain {
                name: COPRIME.into(),
            },
            AtomicFact::DvdFact(_) | AtomicFact::NotDvdFact(_) => {
                AtomicName::Plain { name: DVD.into() }
            }
            AtomicFact::InjectiveFact(_) | AtomicFact::NotInjectiveFact(_) => AtomicName::Plain {
                name: INJECTIVE.into(),
            },
            AtomicFact::SurjectiveFact(_) | AtomicFact::NotSurjectiveFact(_) => AtomicName::Plain {
                name: SURJECTIVE.into(),
            },
            AtomicFact::BijectiveFact(_) | AtomicFact::NotBijectiveFact(_) => AtomicName::Plain {
                name: BIJECTIVE.into(),
            },
            AtomicFact::IsChoiceFunctionForFact(_) | AtomicFact::NotIsChoiceFunctionForFact(_) => {
                AtomicName::Plain {
                    name: IS_CHOICE_FUNCTION_FOR.into(),
                }
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HasSequenceLimitFact {
    pub fact_id: FactId,
    pub sequence: Obj,
    pub value: Obj,
    pub line_file: Option<SourceLine>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotHasSequenceLimitFact {
    pub fact_id: FactId,
    pub sequence: Obj,
    pub value: Obj,
    pub line_file: Option<SourceLine>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HasFunctionLimitFact {
    pub fact_id: FactId,
    pub function: Obj,
    pub approach: crate::ast::obj::LimitApproach,
    pub value: Obj,
    pub line_file: Option<SourceLine>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotHasFunctionLimitFact {
    pub fact_id: FactId,
    pub function: Obj,
    pub approach: crate::ast::obj::LimitApproach,
    pub value: Obj,
    pub line_file: Option<SourceLine>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HasSequenceLimsupFact {
    pub fact_id: FactId,
    pub sequence: Obj,
    pub value: Obj,
    pub line_file: Option<SourceLine>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HasSequenceLiminfFact {
    pub fact_id: FactId,
    pub sequence: Obj,
    pub value: Obj,
    pub line_file: Option<SourceLine>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotHasSequenceLimsupFact {
    pub fact_id: FactId,
    pub sequence: Obj,
    pub value: Obj,
    pub line_file: Option<SourceLine>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotHasSequenceLiminfFact {
    pub fact_id: FactId,
    pub sequence: Obj,
    pub value: Obj,
    pub line_file: Option<SourceLine>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RealSetBoundFact {
    pub fact_id: FactId,
    pub set: Obj,
    pub bound: Obj,
    pub direction: RealBoundDirection,
    pub line_file: Option<SourceLine>,
}
impl RealSetBoundFact {
    pub fn predicate_name(&self) -> &'static str {
        self.direction.predicate_name()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotRealSetBoundFact {
    pub fact_id: FactId,
    pub set: Obj,
    pub bound: Obj,
    pub direction: RealBoundDirection,
    pub line_file: Option<SourceLine>,
}
impl NotRealSetBoundFact {
    pub fn predicate_name(&self) -> &'static str {
        self.direction.predicate_name()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RealSetBoundedFact {
    pub fact_id: FactId,
    pub set: Obj,
    pub boundedness: RealBoundedness,
    pub line_file: Option<SourceLine>,
}
impl RealSetBoundedFact {
    pub fn predicate_name(&self) -> &'static str {
        self.boundedness.predicate_name()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotRealSetBoundedFact {
    pub fact_id: FactId,
    pub set: Obj,
    pub boundedness: RealBoundedness,
    pub line_file: Option<SourceLine>,
}
impl NotRealSetBoundedFact {
    pub fn predicate_name(&self) -> &'static str {
        self.boundedness.predicate_name()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SequenceAnalysisFact {
    pub fact_id: FactId,
    pub sequence: Obj,
    pub property: SequenceAnalysisProperty,
    pub line_file: Option<SourceLine>,
}
impl SequenceAnalysisFact {
    pub fn predicate_name(&self) -> &'static str {
        self.property.predicate_name()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotSequenceAnalysisFact {
    pub fact_id: FactId,
    pub sequence: Obj,
    pub property: SequenceAnalysisProperty,
    pub line_file: Option<SourceLine>,
}
impl NotSequenceAnalysisFact {
    pub fn predicate_name(&self) -> &'static str {
        self.property.predicate_name()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RealAccumulationFact {
    pub fact_id: FactId,
    pub domain: Obj,
    pub point: Obj,
    pub side: RealApproachSide,
    pub line_file: Option<SourceLine>,
}
impl RealAccumulationFact {
    pub fn predicate_name(&self) -> &'static str {
        self.side.accumulation_name()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotRealAccumulationFact {
    pub fact_id: FactId,
    pub domain: Obj,
    pub point: Obj,
    pub side: RealApproachSide,
    pub line_file: Option<SourceLine>,
}
impl NotRealAccumulationFact {
    pub fn predicate_name(&self) -> &'static str {
        self.side.accumulation_name()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FunctionContinuousAtFact {
    pub fact_id: FactId,
    pub function: Obj,
    pub point: Obj,
    pub side: RealApproachSide,
    pub line_file: Option<SourceLine>,
}
impl FunctionContinuousAtFact {
    pub fn predicate_name(&self) -> &'static str {
        self.side.continuity_name()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotFunctionContinuousAtFact {
    pub fact_id: FactId,
    pub function: Obj,
    pub point: Obj,
    pub side: RealApproachSide,
    pub line_file: Option<SourceLine>,
}
impl NotFunctionContinuousAtFact {
    pub fn predicate_name(&self) -> &'static str {
        self.side.continuity_name()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FunctionContinuousFact {
    pub fact_id: FactId,
    pub function: Obj,
    pub property: FunctionContinuityProperty,
    pub line_file: Option<SourceLine>,
}
impl FunctionContinuousFact {
    pub fn predicate_name(&self) -> &'static str {
        self.property.predicate_name()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotFunctionContinuousFact {
    pub fact_id: FactId,
    pub function: Obj,
    pub property: FunctionContinuityProperty,
    pub line_file: Option<SourceLine>,
}
impl NotFunctionContinuousFact {
    pub fn predicate_name(&self) -> &'static str {
        self.property.predicate_name()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FunctionLipschitzFact {
    pub fact_id: FactId,
    pub function: Obj,
    pub constant: Obj,
    pub line_file: Option<SourceLine>,
}
impl FunctionLipschitzFact {
    pub fn predicate_name(&self) -> &'static str {
        "is_lipschitz"
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotFunctionLipschitzFact {
    pub fact_id: FactId,
    pub function: Obj,
    pub constant: Obj,
    pub line_file: Option<SourceLine>,
}
impl NotFunctionLipschitzFact {
    pub fn predicate_name(&self) -> &'static str {
        "is_lipschitz"
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RealBoundDirection {
    Upper,
    Lower,
}
impl RealBoundDirection {
    pub fn predicate_name(&self) -> &'static str {
        match self {
            Self::Upper => "is_real_upper_bound",
            Self::Lower => "is_real_lower_bound",
        }
    }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RealBoundedness {
    Above,
    Below,
    Both,
}
impl RealBoundedness {
    pub fn predicate_name(&self) -> &'static str {
        match self {
            Self::Above => "is_real_bounded_above",
            Self::Below => "is_real_bounded_below",
            Self::Both => "is_real_bounded",
        }
    }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SequenceAnalysisProperty {
    Nondecreasing,
    Nonincreasing,
    StrictlyIncreasing,
    StrictlyDecreasing,
    BoundedAbove,
    BoundedBelow,
    Bounded,
    Cauchy,
    Convergent,
}
impl SequenceAnalysisProperty {
    pub fn predicate_name(&self) -> &'static str {
        match self {
            Self::Nondecreasing => "is_seq_nondecreasing",
            Self::Nonincreasing => "is_seq_nonincreasing",
            Self::StrictlyIncreasing => "is_seq_strictly_increasing",
            Self::StrictlyDecreasing => "is_seq_strictly_decreasing",
            Self::BoundedAbove => "is_seq_bounded_above",
            Self::BoundedBelow => "is_seq_bounded_below",
            Self::Bounded => "is_seq_bounded",
            Self::Cauchy => "is_seq_cauchy",
            Self::Convergent => "is_seq_convergent",
        }
    }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RealApproachSide {
    Both,
    Left,
    Right,
}
impl RealApproachSide {
    pub fn accumulation_name(&self) -> &'static str {
        match self {
            Self::Both => "is_real_accumulation_at",
            Self::Left => "is_real_accumulation_left",
            Self::Right => "is_real_accumulation_right",
        }
    }
    pub fn continuity_name(&self) -> &'static str {
        match self {
            Self::Both => "is_continuous_at",
            Self::Left => "is_continuous_left",
            Self::Right => "is_continuous_right",
        }
    }
    pub fn limit_approach(&self, point: Obj) -> super::super::obj::LimitApproach {
        use super::super::obj::LimitApproach;
        match self {
            Self::Both => LimitApproach::AtPoint(Box::new(point)),
            Self::Left => LimitApproach::FromLeft(Box::new(point)),
            Self::Right => LimitApproach::FromRight(Box::new(point)),
        }
    }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FunctionContinuityProperty {
    Continuous,
    UniformContinuous,
}
impl FunctionContinuityProperty {
    pub fn predicate_name(&self) -> &'static str {
        match self {
            Self::Continuous => "is_continuous",
            Self::UniformContinuous => "is_uniformly_continuous",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HasDerivativeAtFact {
    pub fact_id: FactId,
    pub function: Obj,
    pub point: Obj,
    pub value: Obj,
    pub line_file: Option<SourceLine>,
}
impl HasDerivativeAtFact {
    pub fn predicate_name(&self) -> &'static str {
        "has_derivative_at"
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotHasDerivativeAtFact {
    pub fact_id: FactId,
    pub function: Obj,
    pub point: Obj,
    pub value: Obj,
    pub line_file: Option<SourceLine>,
}
impl NotHasDerivativeAtFact {
    pub fn predicate_name(&self) -> &'static str {
        "has_derivative_at"
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FunctionDifferentiableAtFact {
    pub fact_id: FactId,
    pub function: Obj,
    pub point: Obj,
    pub line_file: Option<SourceLine>,
}
impl FunctionDifferentiableAtFact {
    pub fn predicate_name(&self) -> &'static str {
        "is_differentiable_at"
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotFunctionDifferentiableAtFact {
    pub fact_id: FactId,
    pub function: Obj,
    pub point: Obj,
    pub line_file: Option<SourceLine>,
}
impl NotFunctionDifferentiableAtFact {
    pub fn predicate_name(&self) -> &'static str {
        "is_differentiable_at"
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HasRiemannIntegralFact {
    pub fact_id: FactId,
    pub function: Obj,
    pub lower: Obj,
    pub upper: Obj,
    pub value: Obj,
    pub line_file: Option<SourceLine>,
}
impl HasRiemannIntegralFact {
    pub fn predicate_name(&self) -> &'static str {
        "has_riemann_integral"
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotHasRiemannIntegralFact {
    pub fact_id: FactId,
    pub function: Obj,
    pub lower: Obj,
    pub upper: Obj,
    pub value: Obj,
    pub line_file: Option<SourceLine>,
}
impl NotHasRiemannIntegralFact {
    pub fn predicate_name(&self) -> &'static str {
        "has_riemann_integral"
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FunctionRiemannIntegrableFact {
    pub fact_id: FactId,
    pub function: Obj,
    pub lower: Obj,
    pub upper: Obj,
    pub line_file: Option<SourceLine>,
}
impl FunctionRiemannIntegrableFact {
    pub fn predicate_name(&self) -> &'static str {
        "is_riemann_integrable"
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotFunctionRiemannIntegrableFact {
    pub fact_id: FactId,
    pub function: Obj,
    pub lower: Obj,
    pub upper: Obj,
    pub line_file: Option<SourceLine>,
}
impl NotFunctionRiemannIntegrableFact {
    pub fn predicate_name(&self) -> &'static str {
        "is_riemann_integrable"
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MultivariableAnalysisFact {
    pub fact_id: FactId,
    pub relation: MultivariableAnalysisRelation,
    pub line_file: Option<SourceLine>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotMultivariableAnalysisFact {
    pub fact_id: FactId,
    pub relation: MultivariableAnalysisRelation,
    pub line_file: Option<SourceLine>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MultivariableAnalysisRelation {
    ScalarLimit(ScalarMultivariableLimitRelation),
    VectorLimit(VectorMultivariableLimitRelation),
    ScalarContinuousAt(ScalarMultivariableContinuousAtRelation),
    VectorContinuousAt(VectorMultivariableContinuousAtRelation),
    PartialDerivativeAt(PartialDerivativeAtRelation),
    SecondPartialDerivativeAt(SecondPartialDerivativeAtRelation),
    ScalarDifferentialAt(ScalarDifferentialAtRelation),
    TotalDerivativeAt(TotalDerivativeAtRelation),
    ScalarDifferentiableAt(ScalarMultivariableDifferentiableAtRelation),
    TotalDifferentiableAt(VectorMultivariableDifferentiableAtRelation),
    GradientAt(GradientAtRelation),
    JacobianAt(JacobianAtRelation),
    HessianAt(HessianAtRelation),
    DivergenceAt(DivergenceAtRelation),
    CurlAt(CurlAtRelation),
    LaplacianAt(LaplacianAtRelation),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ScalarMultivariableLimitRelation {
    pub function: Obj,
    pub point: Obj,
    pub dimension: Obj,
    pub value: Obj,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VectorMultivariableLimitRelation {
    pub function: Obj,
    pub point: Obj,
    pub input_dimension: Obj,
    pub output_dimension: Obj,
    pub value: Obj,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ScalarMultivariableContinuousAtRelation {
    pub function: Obj,
    pub point: Obj,
    pub dimension: Obj,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VectorMultivariableContinuousAtRelation {
    pub function: Obj,
    pub point: Obj,
    pub input_dimension: Obj,
    pub output_dimension: Obj,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PartialDerivativeAtRelation {
    pub function: Obj,
    pub point: Obj,
    pub dimension: Obj,
    pub coordinate: Obj,
    pub value: Obj,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SecondPartialDerivativeAtRelation {
    pub function: Obj,
    pub point: Obj,
    pub dimension: Obj,
    pub first_coordinate: Obj,
    pub second_coordinate: Obj,
    pub value: Obj,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ScalarDifferentialAtRelation {
    pub function: Obj,
    pub point: Obj,
    pub dimension: Obj,
    pub value: Obj,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TotalDerivativeAtRelation {
    pub function: Obj,
    pub point: Obj,
    pub input_dimension: Obj,
    pub output_dimension: Obj,
    pub value: Obj,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ScalarMultivariableDifferentiableAtRelation {
    pub function: Obj,
    pub point: Obj,
    pub dimension: Obj,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VectorMultivariableDifferentiableAtRelation {
    pub function: Obj,
    pub point: Obj,
    pub input_dimension: Obj,
    pub output_dimension: Obj,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GradientAtRelation {
    pub function: Obj,
    pub point: Obj,
    pub dimension: Obj,
    pub value: Obj,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct JacobianAtRelation {
    pub function: Obj,
    pub point: Obj,
    pub input_dimension: Obj,
    pub output_dimension: Obj,
    pub value: Obj,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HessianAtRelation {
    pub function: Obj,
    pub point: Obj,
    pub dimension: Obj,
    pub value: Obj,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DivergenceAtRelation {
    pub function: Obj,
    pub point: Obj,
    pub dimension: Obj,
    pub value: Obj,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CurlAtRelation {
    pub function: Obj,
    pub point: Obj,
    pub value: Obj,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LaplacianAtRelation {
    pub function: Obj,
    pub point: Obj,
    pub dimension: Obj,
    pub value: Obj,
}

impl MultivariableAnalysisRelation {
    pub fn predicate_name(&self) -> &'static str {
        match self {
            Self::ScalarLimit(_) => "has_multi_limit_at",
            Self::VectorLimit(_) => "has_vector_limit_at",
            Self::ScalarContinuousAt(_) => "is_multi_continuous_at",
            Self::VectorContinuousAt(_) => "is_vector_continuous_at",
            Self::PartialDerivativeAt(_) => "has_partial_derivative_at",
            Self::SecondPartialDerivativeAt(_) => "has_second_partial_derivative_at",
            Self::ScalarDifferentialAt(_) => "has_scalar_differential_at",
            Self::TotalDerivativeAt(_) => "has_total_derivative_at",
            Self::ScalarDifferentiableAt(_) => "is_multi_differentiable_at",
            Self::TotalDifferentiableAt(_) => "is_vector_differentiable_at",
            Self::GradientAt(_) => "has_gradient_at",
            Self::JacobianAt(_) => "has_jacobian_at",
            Self::HessianAt(_) => "has_hessian_at",
            Self::DivergenceAt(_) => "has_divergence_at",
            Self::CurlAt(_) => "has_curl_at",
            Self::LaplacianAt(_) => "has_laplacian_at",
        }
    }
    pub fn argument_refs(&self) -> Vec<&Obj> {
        match self {
            Self::ScalarLimit(x) => vec![&x.function, &x.point, &x.dimension, &x.value],
            Self::VectorLimit(x) => vec![
                &x.function,
                &x.point,
                &x.input_dimension,
                &x.output_dimension,
                &x.value,
            ],
            Self::ScalarContinuousAt(x) => vec![&x.function, &x.point, &x.dimension],
            Self::VectorContinuousAt(x) => vec![
                &x.function,
                &x.point,
                &x.input_dimension,
                &x.output_dimension,
            ],
            Self::PartialDerivativeAt(x) => {
                vec![&x.function, &x.point, &x.dimension, &x.coordinate, &x.value]
            }
            Self::SecondPartialDerivativeAt(x) => vec![
                &x.function,
                &x.point,
                &x.dimension,
                &x.first_coordinate,
                &x.second_coordinate,
                &x.value,
            ],
            Self::ScalarDifferentialAt(x) => vec![&x.function, &x.point, &x.dimension, &x.value],
            Self::TotalDerivativeAt(x) => vec![
                &x.function,
                &x.point,
                &x.input_dimension,
                &x.output_dimension,
                &x.value,
            ],
            Self::ScalarDifferentiableAt(x) => vec![&x.function, &x.point, &x.dimension],
            Self::TotalDifferentiableAt(x) => vec![
                &x.function,
                &x.point,
                &x.input_dimension,
                &x.output_dimension,
            ],
            Self::GradientAt(x) => vec![&x.function, &x.point, &x.dimension, &x.value],
            Self::JacobianAt(x) => vec![
                &x.function,
                &x.point,
                &x.input_dimension,
                &x.output_dimension,
                &x.value,
            ],
            Self::HessianAt(x) => vec![&x.function, &x.point, &x.dimension, &x.value],
            Self::DivergenceAt(x) => vec![&x.function, &x.point, &x.dimension, &x.value],
            Self::CurlAt(x) => vec![&x.function, &x.point, &x.value],
            Self::LaplacianAt(x) => vec![&x.function, &x.point, &x.dimension, &x.value],
        }
    }
    pub fn from_name(name: &str, args: &[Obj]) -> Option<Self> {
        Some(match name {
            "has_multi_limit_at" if args.len() == 4 => {
                Self::ScalarLimit(ScalarMultivariableLimitRelation {
                    function: args[0].clone(),
                    point: args[1].clone(),
                    dimension: args[2].clone(),
                    value: args[3].clone(),
                })
            }
            "has_vector_limit_at" if args.len() == 5 => {
                Self::VectorLimit(VectorMultivariableLimitRelation {
                    function: args[0].clone(),
                    point: args[1].clone(),
                    input_dimension: args[2].clone(),
                    output_dimension: args[3].clone(),
                    value: args[4].clone(),
                })
            }
            "is_multi_continuous_at" if args.len() == 3 => {
                Self::ScalarContinuousAt(ScalarMultivariableContinuousAtRelation {
                    function: args[0].clone(),
                    point: args[1].clone(),
                    dimension: args[2].clone(),
                })
            }
            "is_vector_continuous_at" if args.len() == 4 => {
                Self::VectorContinuousAt(VectorMultivariableContinuousAtRelation {
                    function: args[0].clone(),
                    point: args[1].clone(),
                    input_dimension: args[2].clone(),
                    output_dimension: args[3].clone(),
                })
            }
            "has_partial_derivative_at" if args.len() == 5 => {
                Self::PartialDerivativeAt(PartialDerivativeAtRelation {
                    function: args[0].clone(),
                    point: args[1].clone(),
                    dimension: args[2].clone(),
                    coordinate: args[3].clone(),
                    value: args[4].clone(),
                })
            }
            "has_second_partial_derivative_at" if args.len() == 6 => {
                Self::SecondPartialDerivativeAt(SecondPartialDerivativeAtRelation {
                    function: args[0].clone(),
                    point: args[1].clone(),
                    dimension: args[2].clone(),
                    first_coordinate: args[3].clone(),
                    second_coordinate: args[4].clone(),
                    value: args[5].clone(),
                })
            }
            "has_scalar_differential_at" if args.len() == 4 => {
                Self::ScalarDifferentialAt(ScalarDifferentialAtRelation {
                    function: args[0].clone(),
                    point: args[1].clone(),
                    dimension: args[2].clone(),
                    value: args[3].clone(),
                })
            }
            "has_total_derivative_at" if args.len() == 5 => {
                Self::TotalDerivativeAt(TotalDerivativeAtRelation {
                    function: args[0].clone(),
                    point: args[1].clone(),
                    input_dimension: args[2].clone(),
                    output_dimension: args[3].clone(),
                    value: args[4].clone(),
                })
            }
            "is_multi_differentiable_at" if args.len() == 3 => {
                Self::ScalarDifferentiableAt(ScalarMultivariableDifferentiableAtRelation {
                    function: args[0].clone(),
                    point: args[1].clone(),
                    dimension: args[2].clone(),
                })
            }
            "is_vector_differentiable_at" if args.len() == 4 => {
                Self::TotalDifferentiableAt(VectorMultivariableDifferentiableAtRelation {
                    function: args[0].clone(),
                    point: args[1].clone(),
                    input_dimension: args[2].clone(),
                    output_dimension: args[3].clone(),
                })
            }
            "has_gradient_at" if args.len() == 4 => Self::GradientAt(GradientAtRelation {
                function: args[0].clone(),
                point: args[1].clone(),
                dimension: args[2].clone(),
                value: args[3].clone(),
            }),
            "has_jacobian_at" if args.len() == 5 => Self::JacobianAt(JacobianAtRelation {
                function: args[0].clone(),
                point: args[1].clone(),
                input_dimension: args[2].clone(),
                output_dimension: args[3].clone(),
                value: args[4].clone(),
            }),
            "has_hessian_at" if args.len() == 4 => Self::HessianAt(HessianAtRelation {
                function: args[0].clone(),
                point: args[1].clone(),
                dimension: args[2].clone(),
                value: args[3].clone(),
            }),
            "has_divergence_at" if args.len() == 4 => Self::DivergenceAt(DivergenceAtRelation {
                function: args[0].clone(),
                point: args[1].clone(),
                dimension: args[2].clone(),
                value: args[3].clone(),
            }),
            "has_curl_at" if args.len() == 3 => Self::CurlAt(CurlAtRelation {
                function: args[0].clone(),
                point: args[1].clone(),
                value: args[2].clone(),
            }),
            "has_laplacian_at" if args.len() == 4 => Self::LaplacianAt(LaplacianAtRelation {
                function: args[0].clone(),
                point: args[1].clone(),
                dimension: args[2].clone(),
                value: args[3].clone(),
            }),
            _ => return None,
        })
    }
    pub fn with_arguments(&self, args: &[Obj]) -> Self {
        Self::from_name(self.predicate_name(), args).expect("same multivariable relation arity")
    }
    pub fn predicate_arity(name: &str) -> Option<usize> {
        match name {
            "has_multi_limit_at" => Some(4),
            "has_vector_limit_at" => Some(5),
            "is_multi_continuous_at" => Some(3),
            "is_vector_continuous_at" => Some(4),
            "has_partial_derivative_at" => Some(5),
            "has_second_partial_derivative_at" => Some(6),
            "has_scalar_differential_at" => Some(4),
            "has_total_derivative_at" => Some(5),
            "is_multi_differentiable_at" => Some(3),
            "is_vector_differentiable_at" => Some(4),
            "has_gradient_at" => Some(4),
            "has_jacobian_at" => Some(5),
            "has_hessian_at" => Some(4),
            "has_divergence_at" => Some(4),
            "has_curl_at" => Some(3),
            "has_laplacian_at" => Some(4),
            _ => None,
        }
    }
}
