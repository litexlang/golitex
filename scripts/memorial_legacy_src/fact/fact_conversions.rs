//! Conversions from fact payloads into the top-level fact sum type.

use crate::prelude::*;

impl From<AtomicFact> for Fact {
    fn from(atomic_fact: AtomicFact) -> Self {
        Fact::AtomicFact(atomic_fact)
    }
}

impl From<OrFact> for Fact {
    fn from(or_fact: OrFact) -> Self {
        Fact::OrFact(or_fact)
    }
}

impl From<ForallFact> for Fact {
    fn from(forall_fact: ForallFact) -> Self {
        Fact::ForallFact(forall_fact)
    }
}

impl From<ExistFact> for Fact {
    fn from(exist_fact: ExistFact) -> Self {
        Fact::ExistFact(exist_fact)
    }
}

impl From<AndFact> for Fact {
    fn from(and_fact: AndFact) -> Self {
        Fact::AndFact(and_fact)
    }
}

impl From<ChainFact> for Fact {
    fn from(chain_fact: ChainFact) -> Self {
        Fact::ChainFact(chain_fact)
    }
}

impl From<AndChainAtomicFact> for Fact {
    fn from(f: AndChainAtomicFact) -> Self {
        match f {
            AndChainAtomicFact::AtomicFact(a) => a.into(),
            AndChainAtomicFact::AndFact(a) => a.into(),
            AndChainAtomicFact::ChainFact(c) => c.into(),
        }
    }
}

impl From<QuantifierFreeFact> for Fact {
    fn from(f: QuantifierFreeFact) -> Self {
        match f {
            QuantifierFreeFact::AtomicFact(a) => a.into(),
            QuantifierFreeFact::AndFact(a) => a.into(),
            QuantifierFreeFact::ChainFact(c) => c.into(),
            QuantifierFreeFact::OrFact(o) => o.into(),
        }
    }
}

impl From<ForallFactWithIff> for Fact {
    fn from(forall_fact_with_iff: ForallFactWithIff) -> Self {
        Fact::ForallFactWithIff(forall_fact_with_iff)
    }
}

impl From<NotForallFact> for Fact {
    fn from(not_forall_fact: NotForallFact) -> Self {
        Fact::NotForall(not_forall_fact)
    }
}
