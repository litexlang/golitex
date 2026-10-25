//! Enum wrapping conversions for facts.
//! Prefer `leaf.into()` / `atomic.into()` over `AtomicFact::Variant(leaf)`.

impl From<crate::ast::fact::RealSetBoundFact> for AtomicFact {
    fn from(f: crate::ast::fact::RealSetBoundFact) -> Self {
        Self::RealSetBoundFact(f)
    }
}
impl From<crate::ast::fact::RealSetBoundFact> for Fact {
    fn from(f: crate::ast::fact::RealSetBoundFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}
impl From<crate::ast::fact::NotRealSetBoundFact> for AtomicFact {
    fn from(f: crate::ast::fact::NotRealSetBoundFact) -> Self {
        Self::NotRealSetBoundFact(f)
    }
}
impl From<crate::ast::fact::NotRealSetBoundFact> for Fact {
    fn from(f: crate::ast::fact::NotRealSetBoundFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}
impl From<crate::ast::fact::RealSetBoundedFact> for AtomicFact {
    fn from(f: crate::ast::fact::RealSetBoundedFact) -> Self {
        Self::RealSetBoundedFact(f)
    }
}
impl From<crate::ast::fact::RealSetBoundedFact> for Fact {
    fn from(f: crate::ast::fact::RealSetBoundedFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}
impl From<crate::ast::fact::NotRealSetBoundedFact> for AtomicFact {
    fn from(f: crate::ast::fact::NotRealSetBoundedFact) -> Self {
        Self::NotRealSetBoundedFact(f)
    }
}
impl From<crate::ast::fact::NotRealSetBoundedFact> for Fact {
    fn from(f: crate::ast::fact::NotRealSetBoundedFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}
impl From<crate::ast::fact::SequenceAnalysisFact> for AtomicFact {
    fn from(f: crate::ast::fact::SequenceAnalysisFact) -> Self {
        Self::SequenceAnalysisFact(f)
    }
}
impl From<crate::ast::fact::SequenceAnalysisFact> for Fact {
    fn from(f: crate::ast::fact::SequenceAnalysisFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}
impl From<crate::ast::fact::NotSequenceAnalysisFact> for AtomicFact {
    fn from(f: crate::ast::fact::NotSequenceAnalysisFact) -> Self {
        Self::NotSequenceAnalysisFact(f)
    }
}
impl From<crate::ast::fact::NotSequenceAnalysisFact> for Fact {
    fn from(f: crate::ast::fact::NotSequenceAnalysisFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}
impl From<crate::ast::fact::RealAccumulationFact> for AtomicFact {
    fn from(f: crate::ast::fact::RealAccumulationFact) -> Self {
        Self::RealAccumulationFact(f)
    }
}
impl From<crate::ast::fact::RealAccumulationFact> for Fact {
    fn from(f: crate::ast::fact::RealAccumulationFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}
impl From<crate::ast::fact::NotRealAccumulationFact> for AtomicFact {
    fn from(f: crate::ast::fact::NotRealAccumulationFact) -> Self {
        Self::NotRealAccumulationFact(f)
    }
}
impl From<crate::ast::fact::NotRealAccumulationFact> for Fact {
    fn from(f: crate::ast::fact::NotRealAccumulationFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}
impl From<crate::ast::fact::FunctionContinuousAtFact> for AtomicFact {
    fn from(f: crate::ast::fact::FunctionContinuousAtFact) -> Self {
        Self::FunctionContinuousAtFact(f)
    }
}
impl From<crate::ast::fact::FunctionContinuousAtFact> for Fact {
    fn from(f: crate::ast::fact::FunctionContinuousAtFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}
impl From<crate::ast::fact::NotFunctionContinuousAtFact> for AtomicFact {
    fn from(f: crate::ast::fact::NotFunctionContinuousAtFact) -> Self {
        Self::NotFunctionContinuousAtFact(f)
    }
}
impl From<crate::ast::fact::NotFunctionContinuousAtFact> for Fact {
    fn from(f: crate::ast::fact::NotFunctionContinuousAtFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}
impl From<crate::ast::fact::FunctionContinuousFact> for AtomicFact {
    fn from(f: crate::ast::fact::FunctionContinuousFact) -> Self {
        Self::FunctionContinuousFact(f)
    }
}
impl From<crate::ast::fact::FunctionContinuousFact> for Fact {
    fn from(f: crate::ast::fact::FunctionContinuousFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}
impl From<crate::ast::fact::NotFunctionContinuousFact> for AtomicFact {
    fn from(f: crate::ast::fact::NotFunctionContinuousFact) -> Self {
        Self::NotFunctionContinuousFact(f)
    }
}
impl From<crate::ast::fact::NotFunctionContinuousFact> for Fact {
    fn from(f: crate::ast::fact::NotFunctionContinuousFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}
impl From<crate::ast::fact::FunctionLipschitzFact> for AtomicFact {
    fn from(f: crate::ast::fact::FunctionLipschitzFact) -> Self {
        Self::FunctionLipschitzFact(f)
    }
}
impl From<crate::ast::fact::FunctionLipschitzFact> for Fact {
    fn from(f: crate::ast::fact::FunctionLipschitzFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}
impl From<crate::ast::fact::NotFunctionLipschitzFact> for AtomicFact {
    fn from(f: crate::ast::fact::NotFunctionLipschitzFact) -> Self {
        Self::NotFunctionLipschitzFact(f)
    }
}
impl From<crate::ast::fact::NotFunctionLipschitzFact> for Fact {
    fn from(f: crate::ast::fact::NotFunctionLipschitzFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}
impl From<crate::ast::obj::Supremum> for crate::ast::obj::Obj {
    fn from(value: crate::ast::obj::Supremum) -> Self {
        Self::BoundOperator(crate::ast::obj::BoundOperator::Supremum(value))
    }
}
impl From<crate::ast::obj::Infimum> for crate::ast::obj::Obj {
    fn from(value: crate::ast::obj::Infimum) -> Self {
        Self::BoundOperator(crate::ast::obj::BoundOperator::Infimum(value))
    }
}

impl From<crate::ast::obj::Composition> for crate::ast::obj::Obj {
    fn from(value: crate::ast::obj::Composition) -> Self {
        Self::FunctionSpace(crate::ast::obj::FunctionSpace::Composition(value))
    }
}

impl From<crate::ast::obj::Preimage> for crate::ast::obj::Obj {
    fn from(value: crate::ast::obj::Preimage) -> Self {
        Self::FunctionSpace(crate::ast::obj::FunctionSpace::Preimage(value))
    }
}

impl From<crate::ast::obj::PreimageSet> for crate::ast::obj::Obj {
    fn from(value: crate::ast::obj::PreimageSet) -> Self {
        Self::FunctionSpace(crate::ast::obj::FunctionSpace::PreimageSet(value))
    }
}

use crate::ast::fact::{
    AtomicFact, BijectiveFact, CoprimeFact, DvdFact, EqualFact, ExistOrAndChainAtomicFact, Fact,
    GreaterEqualFact, GreaterFact, InFact, InjectiveFact, IsChoiceFunctionForFact, IsFiniteSetFact,
    IsNonemptySetFact, IsSetFact, LessEqualFact, LessFact, NormalAtomicFact, NotBijectiveFact,
    NotCoprimeFact, NotDvdFact, NotEqualFact, NotGreaterEqualFact, NotGreaterFact, NotInFact,
    NotInjectiveFact, NotIsChoiceFunctionForFact, NotIsFiniteSetFact, NotIsNonemptySetFact,
    NotIsSetFact, NotLessEqualFact, NotLessFact, NotNormalAtomicFact, NotPrimeFact,
    NotProperSubsetFact, NotProperSupersetFact, NotSubsetFact, NotSupersetFact, NotSurjectiveFact,
    PrimeFact, ProperSubsetFact, ProperSupersetFact, SubsetFact, SupersetFact, SurjectiveFact,
};

impl From<NormalAtomicFact> for AtomicFact {
    fn from(f: NormalAtomicFact) -> Self {
        AtomicFact::NormalAtomicFact(f)
    }
}

impl From<EqualFact> for AtomicFact {
    fn from(f: EqualFact) -> Self {
        AtomicFact::EqualFact(f)
    }
}

impl From<LessFact> for AtomicFact {
    fn from(f: LessFact) -> Self {
        AtomicFact::LessFact(f)
    }
}

impl From<GreaterFact> for AtomicFact {
    fn from(f: GreaterFact) -> Self {
        AtomicFact::GreaterFact(f)
    }
}

impl From<LessEqualFact> for AtomicFact {
    fn from(f: LessEqualFact) -> Self {
        AtomicFact::LessEqualFact(f)
    }
}

impl From<GreaterEqualFact> for AtomicFact {
    fn from(f: GreaterEqualFact) -> Self {
        AtomicFact::GreaterEqualFact(f)
    }
}

impl From<IsSetFact> for AtomicFact {
    fn from(f: IsSetFact) -> Self {
        AtomicFact::IsSetFact(f)
    }
}

impl From<IsNonemptySetFact> for AtomicFact {
    fn from(f: IsNonemptySetFact) -> Self {
        AtomicFact::IsNonemptySetFact(f)
    }
}

impl From<IsFiniteSetFact> for AtomicFact {
    fn from(f: IsFiniteSetFact) -> Self {
        AtomicFact::IsFiniteSetFact(f)
    }
}

impl From<InFact> for AtomicFact {
    fn from(f: InFact) -> Self {
        AtomicFact::InFact(f)
    }
}

impl From<SubsetFact> for AtomicFact {
    fn from(f: SubsetFact) -> Self {
        AtomicFact::SubsetFact(f)
    }
}

impl From<SupersetFact> for AtomicFact {
    fn from(f: SupersetFact) -> Self {
        AtomicFact::SupersetFact(f)
    }
}

impl From<ProperSubsetFact> for AtomicFact {
    fn from(f: ProperSubsetFact) -> Self {
        AtomicFact::ProperSubsetFact(f)
    }
}

impl From<ProperSupersetFact> for AtomicFact {
    fn from(f: ProperSupersetFact) -> Self {
        AtomicFact::ProperSupersetFact(f)
    }
}

impl From<PrimeFact> for AtomicFact {
    fn from(f: PrimeFact) -> Self {
        AtomicFact::PrimeFact(f)
    }
}

impl From<CoprimeFact> for AtomicFact {
    fn from(f: CoprimeFact) -> Self {
        AtomicFact::CoprimeFact(f)
    }
}

impl From<DvdFact> for AtomicFact {
    fn from(f: DvdFact) -> Self {
        AtomicFact::DvdFact(f)
    }
}

impl From<InjectiveFact> for AtomicFact {
    fn from(f: InjectiveFact) -> Self {
        AtomicFact::InjectiveFact(f)
    }
}

impl From<SurjectiveFact> for AtomicFact {
    fn from(f: SurjectiveFact) -> Self {
        AtomicFact::SurjectiveFact(f)
    }
}

impl From<BijectiveFact> for AtomicFact {
    fn from(f: BijectiveFact) -> Self {
        AtomicFact::BijectiveFact(f)
    }
}

impl From<IsChoiceFunctionForFact> for AtomicFact {
    fn from(f: IsChoiceFunctionForFact) -> Self {
        AtomicFact::IsChoiceFunctionForFact(f)
    }
}

impl From<NotNormalAtomicFact> for AtomicFact {
    fn from(f: NotNormalAtomicFact) -> Self {
        AtomicFact::NotNormalAtomicFact(f)
    }
}

impl From<NotEqualFact> for AtomicFact {
    fn from(f: NotEqualFact) -> Self {
        AtomicFact::NotEqualFact(f)
    }
}

impl From<NotLessFact> for AtomicFact {
    fn from(f: NotLessFact) -> Self {
        AtomicFact::NotLessFact(f)
    }
}

impl From<NotGreaterFact> for AtomicFact {
    fn from(f: NotGreaterFact) -> Self {
        AtomicFact::NotGreaterFact(f)
    }
}

impl From<NotLessEqualFact> for AtomicFact {
    fn from(f: NotLessEqualFact) -> Self {
        AtomicFact::NotLessEqualFact(f)
    }
}

impl From<NotGreaterEqualFact> for AtomicFact {
    fn from(f: NotGreaterEqualFact) -> Self {
        AtomicFact::NotGreaterEqualFact(f)
    }
}

impl From<NotIsSetFact> for AtomicFact {
    fn from(f: NotIsSetFact) -> Self {
        AtomicFact::NotIsSetFact(f)
    }
}

impl From<NotIsNonemptySetFact> for AtomicFact {
    fn from(f: NotIsNonemptySetFact) -> Self {
        AtomicFact::NotIsNonemptySetFact(f)
    }
}

impl From<NotIsFiniteSetFact> for AtomicFact {
    fn from(f: NotIsFiniteSetFact) -> Self {
        AtomicFact::NotIsFiniteSetFact(f)
    }
}

impl From<NotInFact> for AtomicFact {
    fn from(f: NotInFact) -> Self {
        AtomicFact::NotInFact(f)
    }
}

impl From<NotSubsetFact> for AtomicFact {
    fn from(f: NotSubsetFact) -> Self {
        AtomicFact::NotSubsetFact(f)
    }
}

impl From<NotSupersetFact> for AtomicFact {
    fn from(f: NotSupersetFact) -> Self {
        AtomicFact::NotSupersetFact(f)
    }
}

impl From<NotProperSubsetFact> for AtomicFact {
    fn from(f: NotProperSubsetFact) -> Self {
        AtomicFact::NotProperSubsetFact(f)
    }
}

impl From<NotProperSupersetFact> for AtomicFact {
    fn from(f: NotProperSupersetFact) -> Self {
        AtomicFact::NotProperSupersetFact(f)
    }
}

impl From<NotPrimeFact> for AtomicFact {
    fn from(f: NotPrimeFact) -> Self {
        AtomicFact::NotPrimeFact(f)
    }
}

impl From<NotCoprimeFact> for AtomicFact {
    fn from(f: NotCoprimeFact) -> Self {
        AtomicFact::NotCoprimeFact(f)
    }
}

impl From<NotDvdFact> for AtomicFact {
    fn from(f: NotDvdFact) -> Self {
        AtomicFact::NotDvdFact(f)
    }
}

impl From<NotInjectiveFact> for AtomicFact {
    fn from(f: NotInjectiveFact) -> Self {
        AtomicFact::NotInjectiveFact(f)
    }
}

impl From<NotSurjectiveFact> for AtomicFact {
    fn from(f: NotSurjectiveFact) -> Self {
        AtomicFact::NotSurjectiveFact(f)
    }
}

impl From<NotBijectiveFact> for AtomicFact {
    fn from(f: NotBijectiveFact) -> Self {
        AtomicFact::NotBijectiveFact(f)
    }
}

impl From<NotIsChoiceFunctionForFact> for AtomicFact {
    fn from(f: NotIsChoiceFunctionForFact) -> Self {
        AtomicFact::NotIsChoiceFunctionForFact(f)
    }
}

impl From<AtomicFact> for Fact {
    fn from(f: AtomicFact) -> Self {
        Fact::AtomicFact(f)
    }
}

impl From<NormalAtomicFact> for Fact {
    fn from(f: NormalAtomicFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}

impl From<EqualFact> for Fact {
    fn from(f: EqualFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}

impl From<LessFact> for Fact {
    fn from(f: LessFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}

impl From<GreaterFact> for Fact {
    fn from(f: GreaterFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}

impl From<LessEqualFact> for Fact {
    fn from(f: LessEqualFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}

impl From<GreaterEqualFact> for Fact {
    fn from(f: GreaterEqualFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}

impl From<IsSetFact> for Fact {
    fn from(f: IsSetFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}

impl From<IsNonemptySetFact> for Fact {
    fn from(f: IsNonemptySetFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}

impl From<IsFiniteSetFact> for Fact {
    fn from(f: IsFiniteSetFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}

impl From<InFact> for Fact {
    fn from(f: InFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}

impl From<SubsetFact> for Fact {
    fn from(f: SubsetFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}

impl From<SupersetFact> for Fact {
    fn from(f: SupersetFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}

impl From<ProperSubsetFact> for Fact {
    fn from(f: ProperSubsetFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}

impl From<ProperSupersetFact> for Fact {
    fn from(f: ProperSupersetFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}

impl From<PrimeFact> for Fact {
    fn from(f: PrimeFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}

impl From<CoprimeFact> for Fact {
    fn from(f: CoprimeFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}

impl From<DvdFact> for Fact {
    fn from(f: DvdFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}

impl From<InjectiveFact> for Fact {
    fn from(f: InjectiveFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}

impl From<SurjectiveFact> for Fact {
    fn from(f: SurjectiveFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}

impl From<BijectiveFact> for Fact {
    fn from(f: BijectiveFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}

impl From<IsChoiceFunctionForFact> for Fact {
    fn from(f: IsChoiceFunctionForFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}

impl From<NotNormalAtomicFact> for Fact {
    fn from(f: NotNormalAtomicFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}

impl From<NotEqualFact> for Fact {
    fn from(f: NotEqualFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}

impl From<NotLessFact> for Fact {
    fn from(f: NotLessFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}

impl From<NotGreaterFact> for Fact {
    fn from(f: NotGreaterFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}

impl From<NotLessEqualFact> for Fact {
    fn from(f: NotLessEqualFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}

impl From<NotGreaterEqualFact> for Fact {
    fn from(f: NotGreaterEqualFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}

impl From<NotIsSetFact> for Fact {
    fn from(f: NotIsSetFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}

impl From<NotIsNonemptySetFact> for Fact {
    fn from(f: NotIsNonemptySetFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}

impl From<NotIsFiniteSetFact> for Fact {
    fn from(f: NotIsFiniteSetFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}

impl From<NotInFact> for Fact {
    fn from(f: NotInFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}

impl From<NotSubsetFact> for Fact {
    fn from(f: NotSubsetFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}

impl From<NotSupersetFact> for Fact {
    fn from(f: NotSupersetFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}

impl From<NotProperSubsetFact> for Fact {
    fn from(f: NotProperSubsetFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}

impl From<NotProperSupersetFact> for Fact {
    fn from(f: NotProperSupersetFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}

impl From<NotPrimeFact> for Fact {
    fn from(f: NotPrimeFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}

impl From<NotCoprimeFact> for Fact {
    fn from(f: NotCoprimeFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}

impl From<NotDvdFact> for Fact {
    fn from(f: NotDvdFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}

impl From<NotInjectiveFact> for Fact {
    fn from(f: NotInjectiveFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}

impl From<NotSurjectiveFact> for Fact {
    fn from(f: NotSurjectiveFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}

impl From<NotBijectiveFact> for Fact {
    fn from(f: NotBijectiveFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}

impl From<NotIsChoiceFunctionForFact> for Fact {
    fn from(f: NotIsChoiceFunctionForFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}

impl From<ExistOrAndChainAtomicFact> for Fact {
    fn from(f: ExistOrAndChainAtomicFact) -> Self {
        match f {
            ExistOrAndChainAtomicFact::AtomicFact(a) => Fact::AtomicFact(a),
            ExistOrAndChainAtomicFact::AndFact(a) => Fact::AndFact(a),
            ExistOrAndChainAtomicFact::ChainFact(c) => Fact::ChainFact(c),
            ExistOrAndChainAtomicFact::OrFact(o) => Fact::OrFact(o),
            ExistOrAndChainAtomicFact::ExistFact(e) => Fact::ExistFact(e),
            ExistOrAndChainAtomicFact::ExistUniqueFact(e) => Fact::ExistUniqueFact(e),
            ExistOrAndChainAtomicFact::NotExistFact(e) => Fact::NotExistFact(e),
        }
    }
}

impl From<crate::ast::obj::Sec> for crate::ast::obj::Obj {
    fn from(value: crate::ast::obj::Sec) -> Self {
        Self::TrigOperator(crate::ast::obj::TrigOperator::Sec(value))
    }
}

impl crate::ast::obj::Sec {
    pub fn new(arg: crate::ast::obj::Obj) -> Self {
        Self { arg: Box::new(arg) }
    }
}

impl From<crate::ast::obj::Csc> for crate::ast::obj::Obj {
    fn from(value: crate::ast::obj::Csc) -> Self {
        Self::TrigOperator(crate::ast::obj::TrigOperator::Csc(value))
    }
}

impl crate::ast::obj::Csc {
    pub fn new(arg: crate::ast::obj::Obj) -> Self {
        Self { arg: Box::new(arg) }
    }
}

impl From<crate::ast::obj::Conjugate> for crate::ast::obj::Obj {
    fn from(value: crate::ast::obj::Conjugate) -> Self {
        Self::ComplexOperator(crate::ast::obj::ComplexOperator::Conjugate(value))
    }
}

impl crate::ast::obj::Conjugate {
    pub fn new(arg: crate::ast::obj::Obj) -> Self {
        Self { arg: Box::new(arg) }
    }
}

impl From<crate::ast::obj::Sinh> for crate::ast::obj::Obj {
    fn from(value: crate::ast::obj::Sinh) -> Self {
        Self::HyperbolicOperator(crate::ast::obj::HyperbolicOperator::Sinh(value))
    }
}

impl crate::ast::obj::Sinh {
    pub fn new(arg: crate::ast::obj::Obj) -> Self {
        Self { arg: Box::new(arg) }
    }
}

impl From<crate::ast::obj::Cosh> for crate::ast::obj::Obj {
    fn from(value: crate::ast::obj::Cosh) -> Self {
        Self::HyperbolicOperator(crate::ast::obj::HyperbolicOperator::Cosh(value))
    }
}

impl crate::ast::obj::Cosh {
    pub fn new(arg: crate::ast::obj::Obj) -> Self {
        Self { arg: Box::new(arg) }
    }
}

impl From<crate::ast::obj::Tanh> for crate::ast::obj::Obj {
    fn from(value: crate::ast::obj::Tanh) -> Self {
        Self::HyperbolicOperator(crate::ast::obj::HyperbolicOperator::Tanh(value))
    }
}

impl crate::ast::obj::Tanh {
    pub fn new(arg: crate::ast::obj::Obj) -> Self {
        Self { arg: Box::new(arg) }
    }
}

impl From<crate::ast::obj::Coth> for crate::ast::obj::Obj {
    fn from(value: crate::ast::obj::Coth) -> Self {
        Self::HyperbolicOperator(crate::ast::obj::HyperbolicOperator::Coth(value))
    }
}

impl crate::ast::obj::Coth {
    pub fn new(arg: crate::ast::obj::Obj) -> Self {
        Self { arg: Box::new(arg) }
    }
}

impl From<crate::ast::obj::Sech> for crate::ast::obj::Obj {
    fn from(value: crate::ast::obj::Sech) -> Self {
        Self::HyperbolicOperator(crate::ast::obj::HyperbolicOperator::Sech(value))
    }
}

impl crate::ast::obj::Sech {
    pub fn new(arg: crate::ast::obj::Obj) -> Self {
        Self { arg: Box::new(arg) }
    }
}

impl From<crate::ast::obj::Csch> for crate::ast::obj::Obj {
    fn from(value: crate::ast::obj::Csch) -> Self {
        Self::HyperbolicOperator(crate::ast::obj::HyperbolicOperator::Csch(value))
    }
}

impl crate::ast::obj::Csch {
    pub fn new(arg: crate::ast::obj::Obj) -> Self {
        Self { arg: Box::new(arg) }
    }
}

impl From<crate::ast::obj::SymmetricDifference> for crate::ast::obj::Obj {
    fn from(value: crate::ast::obj::SymmetricDifference) -> Self {
        Self::SetOperator(crate::ast::obj::SetOperator::SymmetricDifference(value))
    }
}

impl crate::ast::obj::SymmetricDifference {
    pub fn new(left: crate::ast::obj::Obj, right: crate::ast::obj::Obj) -> Self {
        Self {
            left: Box::new(left),
            right: Box::new(right),
        }
    }
}

impl From<crate::ast::fact::HasSequenceLimitFact> for AtomicFact {
    fn from(f: crate::ast::fact::HasSequenceLimitFact) -> Self {
        AtomicFact::HasSequenceLimitFact(f)
    }
}
impl From<crate::ast::fact::HasSequenceLimitFact> for Fact {
    fn from(f: crate::ast::fact::HasSequenceLimitFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}

impl From<crate::ast::fact::NotHasSequenceLimitFact> for AtomicFact {
    fn from(f: crate::ast::fact::NotHasSequenceLimitFact) -> Self {
        AtomicFact::NotHasSequenceLimitFact(f)
    }
}
impl From<crate::ast::fact::NotHasSequenceLimitFact> for Fact {
    fn from(f: crate::ast::fact::NotHasSequenceLimitFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}

impl From<crate::ast::obj::SequenceLimit> for crate::ast::obj::Obj {
    fn from(value: crate::ast::obj::SequenceLimit) -> Self {
        crate::ast::obj::Obj::LimitOperator(crate::ast::obj::LimitOperator::Sequence(value))
    }
}

impl From<crate::ast::fact::HasFunctionLimitFact> for AtomicFact {
    fn from(f: crate::ast::fact::HasFunctionLimitFact) -> Self {
        Self::HasFunctionLimitFact(f)
    }
}
impl From<crate::ast::fact::HasFunctionLimitFact> for Fact {
    fn from(f: crate::ast::fact::HasFunctionLimitFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}

impl From<crate::ast::fact::NotHasFunctionLimitFact> for AtomicFact {
    fn from(f: crate::ast::fact::NotHasFunctionLimitFact) -> Self {
        Self::NotHasFunctionLimitFact(f)
    }
}
impl From<crate::ast::fact::NotHasFunctionLimitFact> for Fact {
    fn from(f: crate::ast::fact::NotHasFunctionLimitFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}

impl From<crate::ast::fact::HasSequenceLimsupFact> for AtomicFact {
    fn from(f: crate::ast::fact::HasSequenceLimsupFact) -> Self {
        AtomicFact::HasSequenceLimsupFact(f)
    }
}
impl From<crate::ast::fact::HasSequenceLimsupFact> for Fact {
    fn from(f: crate::ast::fact::HasSequenceLimsupFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}

impl From<crate::ast::fact::NotHasSequenceLimsupFact> for AtomicFact {
    fn from(f: crate::ast::fact::NotHasSequenceLimsupFact) -> Self {
        AtomicFact::NotHasSequenceLimsupFact(f)
    }
}
impl From<crate::ast::fact::NotHasSequenceLimsupFact> for Fact {
    fn from(f: crate::ast::fact::NotHasSequenceLimsupFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}

impl From<crate::ast::obj::SequenceLimsup> for crate::ast::obj::Obj {
    fn from(value: crate::ast::obj::SequenceLimsup) -> Self {
        crate::ast::obj::Obj::LimitOperator(crate::ast::obj::LimitOperator::SequenceLimsup(value))
    }
}

impl From<crate::ast::fact::HasSequenceLiminfFact> for AtomicFact {
    fn from(f: crate::ast::fact::HasSequenceLiminfFact) -> Self {
        AtomicFact::HasSequenceLiminfFact(f)
    }
}
impl From<crate::ast::fact::HasSequenceLiminfFact> for Fact {
    fn from(f: crate::ast::fact::HasSequenceLiminfFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}

impl From<crate::ast::fact::NotHasSequenceLiminfFact> for AtomicFact {
    fn from(f: crate::ast::fact::NotHasSequenceLiminfFact) -> Self {
        AtomicFact::NotHasSequenceLiminfFact(f)
    }
}
impl From<crate::ast::fact::NotHasSequenceLiminfFact> for Fact {
    fn from(f: crate::ast::fact::NotHasSequenceLiminfFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}

impl From<crate::ast::obj::SequenceLiminf> for crate::ast::obj::Obj {
    fn from(value: crate::ast::obj::SequenceLiminf) -> Self {
        crate::ast::obj::Obj::LimitOperator(crate::ast::obj::LimitOperator::SequenceLiminf(value))
    }
}

impl From<crate::ast::obj::FunctionLimit> for crate::ast::obj::Obj {
    fn from(value: crate::ast::obj::FunctionLimit) -> Self {
        Self::LimitOperator(crate::ast::obj::LimitOperator::Function(value))
    }
}

impl From<crate::ast::fact::HasDerivativeAtFact> for AtomicFact {
    fn from(f: crate::ast::fact::HasDerivativeAtFact) -> Self {
        Self::HasDerivativeAtFact(f)
    }
}
impl From<crate::ast::fact::HasDerivativeAtFact> for Fact {
    fn from(f: crate::ast::fact::HasDerivativeAtFact) -> Self {
        Self::AtomicFact(f.into())
    }
}

impl From<crate::ast::fact::NotHasDerivativeAtFact> for AtomicFact {
    fn from(f: crate::ast::fact::NotHasDerivativeAtFact) -> Self {
        Self::NotHasDerivativeAtFact(f)
    }
}
impl From<crate::ast::fact::NotHasDerivativeAtFact> for Fact {
    fn from(f: crate::ast::fact::NotHasDerivativeAtFact) -> Self {
        Self::AtomicFact(f.into())
    }
}

impl From<crate::ast::fact::FunctionDifferentiableAtFact> for AtomicFact {
    fn from(f: crate::ast::fact::FunctionDifferentiableAtFact) -> Self {
        Self::FunctionDifferentiableAtFact(f)
    }
}
impl From<crate::ast::fact::FunctionDifferentiableAtFact> for Fact {
    fn from(f: crate::ast::fact::FunctionDifferentiableAtFact) -> Self {
        Self::AtomicFact(f.into())
    }
}

impl From<crate::ast::fact::NotFunctionDifferentiableAtFact> for AtomicFact {
    fn from(f: crate::ast::fact::NotFunctionDifferentiableAtFact) -> Self {
        Self::NotFunctionDifferentiableAtFact(f)
    }
}
impl From<crate::ast::fact::NotFunctionDifferentiableAtFact> for Fact {
    fn from(f: crate::ast::fact::NotFunctionDifferentiableAtFact) -> Self {
        Self::AtomicFact(f.into())
    }
}

impl From<crate::ast::obj::DerivativeAt> for crate::ast::obj::Obj {
    fn from(v: crate::ast::obj::DerivativeAt) -> Self {
        Self::DerivativeOperator(crate::ast::obj::DerivativeOperator::AtPoint(v))
    }
}
impl From<crate::ast::fact::HasRiemannIntegralFact> for AtomicFact {
    fn from(f: crate::ast::fact::HasRiemannIntegralFact) -> Self {
        Self::HasRiemannIntegralFact(f)
    }
}
impl From<crate::ast::fact::HasRiemannIntegralFact> for Fact {
    fn from(f: crate::ast::fact::HasRiemannIntegralFact) -> Self {
        Self::AtomicFact(f.into())
    }
}
impl From<crate::ast::fact::NotHasRiemannIntegralFact> for AtomicFact {
    fn from(f: crate::ast::fact::NotHasRiemannIntegralFact) -> Self {
        Self::NotHasRiemannIntegralFact(f)
    }
}
impl From<crate::ast::fact::NotHasRiemannIntegralFact> for Fact {
    fn from(f: crate::ast::fact::NotHasRiemannIntegralFact) -> Self {
        Self::AtomicFact(f.into())
    }
}
impl From<crate::ast::fact::FunctionRiemannIntegrableFact> for AtomicFact {
    fn from(f: crate::ast::fact::FunctionRiemannIntegrableFact) -> Self {
        Self::FunctionRiemannIntegrableFact(f)
    }
}
impl From<crate::ast::fact::FunctionRiemannIntegrableFact> for Fact {
    fn from(f: crate::ast::fact::FunctionRiemannIntegrableFact) -> Self {
        Self::AtomicFact(f.into())
    }
}
impl From<crate::ast::fact::NotFunctionRiemannIntegrableFact> for AtomicFact {
    fn from(f: crate::ast::fact::NotFunctionRiemannIntegrableFact) -> Self {
        Self::NotFunctionRiemannIntegrableFact(f)
    }
}
impl From<crate::ast::fact::NotFunctionRiemannIntegrableFact> for Fact {
    fn from(f: crate::ast::fact::NotFunctionRiemannIntegrableFact) -> Self {
        Self::AtomicFact(f.into())
    }
}
impl From<crate::ast::obj::RiemannIntegral> for crate::ast::obj::Obj {
    fn from(v: crate::ast::obj::RiemannIntegral) -> Self {
        Self::IntegralOperator(crate::ast::obj::IntegralOperator::Riemann(v))
    }
}

impl From<crate::ast::obj::MatrixOperator> for crate::ast::obj::Obj {
    fn from(value: crate::ast::obj::MatrixOperator) -> Self {
        Self::MatrixOperator(value)
    }
}
impl From<crate::ast::obj::MatrixSet> for crate::ast::obj::Obj {
    fn from(value: crate::ast::obj::MatrixSet) -> Self {
        Self::SetFormer(crate::ast::obj::SetFormer::MatrixSet(value))
    }
}

impl From<crate::ast::obj::MultivariableScalarLimit> for crate::ast::obj::Obj {
    fn from(x: crate::ast::obj::MultivariableScalarLimit) -> Self {
        Self::LimitOperator(crate::ast::obj::LimitOperator::MultivariableScalar(x))
    }
}

impl From<crate::ast::obj::MultivariableVectorLimit> for crate::ast::obj::Obj {
    fn from(x: crate::ast::obj::MultivariableVectorLimit) -> Self {
        Self::LimitOperator(crate::ast::obj::LimitOperator::MultivariableVector(x))
    }
}

impl From<crate::ast::obj::PartialDerivativeAt> for crate::ast::obj::Obj {
    fn from(x: crate::ast::obj::PartialDerivativeAt) -> Self {
        Self::DerivativeOperator(crate::ast::obj::DerivativeOperator::Partial(x))
    }
}

impl From<crate::ast::obj::ScalarDifferentialAt> for crate::ast::obj::Obj {
    fn from(x: crate::ast::obj::ScalarDifferentialAt) -> Self {
        Self::DerivativeOperator(crate::ast::obj::DerivativeOperator::ScalarDifferential(x))
    }
}

impl From<crate::ast::obj::TotalDifferentialAt> for crate::ast::obj::Obj {
    fn from(x: crate::ast::obj::TotalDifferentialAt) -> Self {
        Self::DerivativeOperator(crate::ast::obj::DerivativeOperator::TotalDifferential(x))
    }
}

impl From<crate::ast::obj::GradientAt> for crate::ast::obj::Obj {
    fn from(x: crate::ast::obj::GradientAt) -> Self {
        Self::DerivativeOperator(crate::ast::obj::DerivativeOperator::Gradient(x))
    }
}

impl From<crate::ast::obj::JacobianAt> for crate::ast::obj::Obj {
    fn from(x: crate::ast::obj::JacobianAt) -> Self {
        Self::DerivativeOperator(crate::ast::obj::DerivativeOperator::Jacobian(x))
    }
}

impl From<crate::ast::obj::HessianAt> for crate::ast::obj::Obj {
    fn from(x: crate::ast::obj::HessianAt) -> Self {
        Self::DerivativeOperator(crate::ast::obj::DerivativeOperator::Hessian(x))
    }
}

impl From<crate::ast::obj::DivergenceAt> for crate::ast::obj::Obj {
    fn from(x: crate::ast::obj::DivergenceAt) -> Self {
        Self::DerivativeOperator(crate::ast::obj::DerivativeOperator::Divergence(x))
    }
}

impl From<crate::ast::obj::CurlAt> for crate::ast::obj::Obj {
    fn from(x: crate::ast::obj::CurlAt) -> Self {
        Self::DerivativeOperator(crate::ast::obj::DerivativeOperator::Curl(x))
    }
}

impl From<crate::ast::obj::LaplacianAt> for crate::ast::obj::Obj {
    fn from(x: crate::ast::obj::LaplacianAt) -> Self {
        Self::DerivativeOperator(crate::ast::obj::DerivativeOperator::Laplacian(x))
    }
}

impl From<crate::ast::fact::MultivariableAnalysisFact> for AtomicFact {
    fn from(x: crate::ast::fact::MultivariableAnalysisFact) -> Self {
        Self::MultivariableAnalysisFact(x)
    }
}
impl From<crate::ast::fact::MultivariableAnalysisFact> for Fact {
    fn from(x: crate::ast::fact::MultivariableAnalysisFact) -> Self {
        AtomicFact::from(x).into()
    }
}

impl From<crate::ast::fact::NotMultivariableAnalysisFact> for AtomicFact {
    fn from(x: crate::ast::fact::NotMultivariableAnalysisFact) -> Self {
        Self::NotMultivariableAnalysisFact(x)
    }
}
impl From<crate::ast::fact::NotMultivariableAnalysisFact> for Fact {
    fn from(x: crate::ast::fact::NotMultivariableAnalysisFact) -> Self {
        AtomicFact::from(x).into()
    }
}
