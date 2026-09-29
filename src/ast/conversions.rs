//! Enum wrapping conversions for facts.
//! Prefer `leaf.into()` / `atomic.into()` over `AtomicFact::Variant(leaf)`.

use crate::ast::fact::{
    AtomicFact, BijectiveFact, CoprimeFact, DvdFact, EqualFact, ExistOrAndChainAtomicFact, Fact,
    GreaterEqualFact, GreaterFact, InFact, InjectiveFact, IsCartFact, IsChoiceFunctionForFact,
    IsFiniteSetFact, IsNonemptySetFact, IsSetFact, IsTupleFact, LessEqualFact, LessFact,
    NormalAtomicFact, NotBijectiveFact, NotCoprimeFact, NotDvdFact, NotEqualFact,
    NotGreaterEqualFact, NotGreaterFact, NotInFact, NotInjectiveFact, NotIsCartFact,
    NotIsChoiceFunctionForFact, NotIsFiniteSetFact, NotIsNonemptySetFact, NotIsSetFact,
    NotIsTupleFact, NotLessEqualFact, NotLessFact, NotNormalAtomicFact, NotPrimeFact,
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

impl From<IsCartFact> for AtomicFact {
    fn from(f: IsCartFact) -> Self {
        AtomicFact::IsCartFact(f)
    }
}

impl From<IsTupleFact> for AtomicFact {
    fn from(f: IsTupleFact) -> Self {
        AtomicFact::IsTupleFact(f)
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

impl From<NotIsCartFact> for AtomicFact {
    fn from(f: NotIsCartFact) -> Self {
        AtomicFact::NotIsCartFact(f)
    }
}

impl From<NotIsTupleFact> for AtomicFact {
    fn from(f: NotIsTupleFact) -> Self {
        AtomicFact::NotIsTupleFact(f)
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

impl From<IsCartFact> for Fact {
    fn from(f: IsCartFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}

impl From<IsTupleFact> for Fact {
    fn from(f: IsTupleFact) -> Self {
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

impl From<NotIsCartFact> for Fact {
    fn from(f: NotIsCartFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}

impl From<NotIsTupleFact> for Fact {
    fn from(f: NotIsTupleFact) -> Self {
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
