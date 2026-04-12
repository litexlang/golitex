use crate::prelude::*;
use std::fmt;

#[derive(Clone)]
pub enum ExistOrAndChainAtomicFact {
    AtomicFact(AtomicFact),
    AndFact(AndFact),
    ChainFact(ChainFact),
    OrFact(OrFact),
    ExistFact(ExistFact),
}

impl fmt::Display for ExistOrAndChainAtomicFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ExistOrAndChainAtomicFact::AtomicFact(atomic_fact) => write!(f, "{}", atomic_fact),
            ExistOrAndChainAtomicFact::AndFact(and_fact) => write!(f, "{}", and_fact),
            ExistOrAndChainAtomicFact::ChainFact(chain_fact) => write!(f, "{}", chain_fact),
            ExistOrAndChainAtomicFact::OrFact(or_fact) => write!(f, "{}", or_fact),
            ExistOrAndChainAtomicFact::ExistFact(exist_fact) => write!(f, "{}", exist_fact),
        }
    }
}

impl ExistOrAndChainAtomicFact {
    pub fn to_fact(self) -> Fact {
        match self {
            ExistOrAndChainAtomicFact::AtomicFact(atomic_fact) => Fact::AtomicFact(atomic_fact),
            ExistOrAndChainAtomicFact::AndFact(and_fact) => Fact::AndFact(and_fact),
            ExistOrAndChainAtomicFact::ChainFact(chain_fact) => Fact::ChainFact(chain_fact),
            ExistOrAndChainAtomicFact::OrFact(or_fact) => Fact::OrFact(or_fact),
            ExistOrAndChainAtomicFact::ExistFact(exist_fact) => Fact::ExistFact(exist_fact),
        }
    }

    pub fn line_file(&self) -> LineFile {
        match self {
            ExistOrAndChainAtomicFact::AtomicFact(atomic_fact) => atomic_fact.line_file(),
            ExistOrAndChainAtomicFact::AndFact(and_fact) => and_fact.line_file(),
            ExistOrAndChainAtomicFact::ChainFact(chain_fact) => chain_fact.line_file(),
            ExistOrAndChainAtomicFact::OrFact(or_fact) => or_fact.line_file.clone(),
            ExistOrAndChainAtomicFact::ExistFact(exist_fact) => exist_fact.line_file(),
        }
    }
}

impl From<AtomicFact> for ExistOrAndChainAtomicFact {
    fn from(atomic_fact: AtomicFact) -> Self {
        ExistOrAndChainAtomicFact::AtomicFact(atomic_fact)
    }
}

impl From<GreaterEqualFact> for ExistOrAndChainAtomicFact {
    fn from(f: GreaterEqualFact) -> Self {
        AtomicFact::from(f).into()
    }
}

impl From<IsNonemptySetFact> for ExistOrAndChainAtomicFact {
    fn from(f: IsNonemptySetFact) -> Self {
        AtomicFact::from(f).into()
    }
}

impl From<EqualFact> for ExistOrAndChainAtomicFact {
    fn from(f: EqualFact) -> Self {
        AtomicFact::from(f).into()
    }
}

impl From<InFact> for ExistOrAndChainAtomicFact {
    fn from(f: InFact) -> Self {
        ExistOrAndChainAtomicFact::AtomicFact(f.into())
    }
}

impl From<ExistFact> for ExistOrAndChainAtomicFact {
    fn from(exist_fact: ExistFact) -> Self {
        ExistOrAndChainAtomicFact::ExistFact(exist_fact)
    }
}

impl From<AndFact> for ExistOrAndChainAtomicFact {
    fn from(a: AndFact) -> Self {
        ExistOrAndChainAtomicFact::AndFact(a)
    }
}

impl From<ChainFact> for ExistOrAndChainAtomicFact {
    fn from(c: ChainFact) -> Self {
        ExistOrAndChainAtomicFact::ChainFact(c)
    }
}

impl From<OrFact> for ExistOrAndChainAtomicFact {
    fn from(o: OrFact) -> Self {
        ExistOrAndChainAtomicFact::OrFact(o)
    }
}
