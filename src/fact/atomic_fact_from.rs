use crate::prelude::*;

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

impl From<FnEqualInFact> for AtomicFact {
    fn from(f: FnEqualInFact) -> Self {
        AtomicFact::FnEqualInFact(f)
    }
}

impl From<FnEqualFact> for AtomicFact {
    fn from(f: FnEqualFact) -> Self {
        AtomicFact::FnEqualFact(f)
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

impl From<FnEqualInFact> for Fact {
    fn from(f: FnEqualInFact) -> Self {
        Fact::AtomicFact(f.into())
    }
}

impl From<FnEqualFact> for Fact {
    fn from(f: FnEqualFact) -> Self {
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
