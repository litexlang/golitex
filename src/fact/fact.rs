use crate::prelude::*;
use std::fmt;
#[derive(Clone)]
pub enum Fact {
    AtomicFact(AtomicFact),
    ExistFact(ExistFact),
    OrFact(OrFact),
    AndFact(AndFact),
    ChainFact(ChainFact),
    ForallFact(ForallFact),
    ForallFactWithIff(ForallFactWithIff),
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
        }
    }

    pub fn into_stmt(self) -> Stmt {
        self.into()
    }
}

impl Fact {
    // TODO 未来删了比较好，因为默认所有stmt里的东西都不能变化了
    pub fn with_new_line_file(self, line_file: LineFile) -> Fact {
        match self {
            Fact::AtomicFact(atomic_fact) => {
                Fact::AtomicFact(atomic_fact.with_new_line_file(line_file))
            }
            Fact::ExistFact(e) => Fact::ExistFact(ExistFact {
                params_def_with_type: e.params_def_with_type,
                facts: e.facts,
                line_file,
            }),
            Fact::OrFact(or_fact) => OrFact::new(or_fact.facts, line_file).into(),
            Fact::AndFact(and_fact) => Fact::AndFact(AndFact::new(and_fact.facts, line_file)),
            Fact::ChainFact(chain_fact) => Fact::ChainFact(ChainFact::new(
                chain_fact.objs,
                chain_fact.prop_names,
                line_file,
            )),
            Fact::ForallFact(f) => Fact::ForallFact(ForallFact {
                params_def_with_type: f.params_def_with_type,
                dom_facts: f.dom_facts,
                then_facts: f.then_facts,
                line_file,
            }),
            Fact::ForallFactWithIff(f) => Fact::ForallFactWithIff(ForallFactWithIff {
                forall_fact: f.forall_fact,
                iff_facts: f.iff_facts,
                line_file,
            }),
        }
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

impl From<ForallFactWithIff> for Fact {
    fn from(forall_fact_with_iff: ForallFactWithIff) -> Self {
        Fact::ForallFactWithIff(forall_fact_with_iff)
    }
}
