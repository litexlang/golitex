use crate::prelude::*;
use std::fmt;
#[derive(Clone)]
pub enum Fact {
    AtomicFact(AtomicFact),
    ExistFact(ExistFactEnum),
    OrFact(OrFact),
    AndFact(AndFact),
    ChainFact(ChainFact),
    ForallFact(ForallFact),
    ForallFactWithIff(ForallFactWithIff),
    NotForall(NotForallFact),
}

impl fmt::Debug for Fact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self)
    }
}

impl Fact {
    pub fn fact_type_string(&self) -> String {
        match self {
            Fact::AtomicFact(_) => "AtomicFact".to_string(),
            Fact::ExistFact(_) => "ExistFact".to_string(),
            Fact::OrFact(_) => "OrFact".to_string(),
            Fact::AndFact(_) => "AndFact".to_string(),
            Fact::ChainFact(_) => "ChainFact".to_string(),
            Fact::ForallFact(_) => "ForallFact".to_string(),
            Fact::ForallFactWithIff(_) => "ForallFactWithIff".to_string(),
            Fact::NotForall(_) => "NotForallFact".to_string(),
        }
    }
}

impl fmt::Display for Fact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Fact::AtomicFact(atomic_fact) => write!(f, "{}", atomic_fact),
            Fact::ExistFact(exist_fact) => write!(f, "{}", exist_fact),
            Fact::OrFact(or_fact) => write!(f, "{}", or_fact),
            Fact::AndFact(and_fact) => write!(f, "{}", and_fact),
            Fact::ChainFact(chain_fact) => write!(f, "{}", chain_fact),
            Fact::ForallFact(forall_fact) => write!(f, "{}", forall_fact),
            Fact::ForallFactWithIff(forall_fact_with_iff) => write!(f, "{}", forall_fact_with_iff),
            Fact::NotForall(not_forall) => write!(f, "{}", not_forall),
        }
    }
}

impl Fact {
    pub fn line_file(&self) -> LineFile {
        match self {
            Fact::AtomicFact(a) => a.line_file(),
            Fact::ExistFact(e) => e.line_file(),
            Fact::OrFact(o) => o.line_file.clone(),
            Fact::AndFact(a) => a.line_file(),
            Fact::ChainFact(c) => c.line_file(),
            Fact::ForallFact(f) => f.line_file.clone(),
            Fact::ForallFactWithIff(f) => f.line_file.clone(),
            Fact::NotForall(f) => f.line_file(),
        }
    }

    pub fn with_line_file(self, line_file: LineFile) -> Self {
        match self {
            Fact::AtomicFact(a) => Fact::AtomicFact(a.with_line_file(line_file)),
            Fact::ExistFact(mut e) => {
                match &mut e {
                    ExistFactEnum::ExistFact(b)
                    | ExistFactEnum::ExistUniqueFact(b)
                    | ExistFactEnum::NotExistFact(b) => b.line_file = line_file,
                }
                Fact::ExistFact(e)
            }
            Fact::OrFact(mut o) => {
                o.line_file = line_file;
                Fact::OrFact(o)
            }
            Fact::AndFact(mut a) => {
                a.line_file = line_file;
                Fact::AndFact(a)
            }
            Fact::ChainFact(mut c) => {
                c.line_file = line_file;
                Fact::ChainFact(c)
            }
            Fact::ForallFact(mut f) => {
                f.line_file = line_file;
                Fact::ForallFact(f)
            }
            Fact::ForallFactWithIff(mut f) => {
                f.line_file = line_file;
                Fact::ForallFactWithIff(f)
            }
            Fact::NotForall(mut f) => {
                f.forall_fact.line_file = line_file;
                Fact::NotForall(f)
            }
        }
    }

    pub fn into_stmt(self) -> Stmt {
        self.into()
    }
}

#[derive(Clone)]
pub struct NotForallFact {
    pub forall_fact: ForallFact,
}

impl NotForallFact {
    pub fn new(forall_fact: ForallFact) -> Self {
        Self { forall_fact }
    }

    pub fn line_file(&self) -> LineFile {
        self.forall_fact.line_file.clone()
    }
}

impl fmt::Display for NotForallFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}", NOT, self.forall_fact)
    }
}

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

impl From<ExistFactEnum> for Fact {
    fn from(exist_fact: ExistFactEnum) -> Self {
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

impl From<OrAndChainAtomicFact> for Fact {
    fn from(f: OrAndChainAtomicFact) -> Self {
        match f {
            OrAndChainAtomicFact::AtomicFact(a) => a.into(),
            OrAndChainAtomicFact::AndFact(a) => a.into(),
            OrAndChainAtomicFact::ChainFact(c) => c.into(),
            OrAndChainAtomicFact::OrFact(o) => o.into(),
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
