use crate::prelude::*;

#[derive(Debug)]
pub enum FactResult {
    AtomicFact(FactStmtResult),
    ExistFact(FactStmtResult),
    OrFact(FactStmtResult),
    AndFact(FactStmtResult),
    ChainFact(FactStmtResult),
    ForallFact(FactStmtResult),
    ForallFactWithIff(FactStmtResult),
    NotForall(FactStmtResult),
}

#[derive(Debug)]
pub enum FactStmtResult {
    Success(FactualStmtSuccess),
    Unknown(Box<FactUnknown>),
}

impl FactResult {
    pub fn new(success: FactualStmtSuccess) -> Self {
        match &success.stmt {
            Fact::AtomicFact(_) => FactResult::AtomicFact(FactStmtResult::Success(success)),
            Fact::ExistFact(_) => FactResult::ExistFact(FactStmtResult::Success(success)),
            Fact::OrFact(_) => FactResult::OrFact(FactStmtResult::Success(success)),
            Fact::AndFact(_) => FactResult::AndFact(FactStmtResult::Success(success)),
            Fact::ChainFact(_) => FactResult::ChainFact(FactStmtResult::Success(success)),
            Fact::ForallFact(_) => FactResult::ForallFact(FactStmtResult::Success(success)),
            Fact::ForallFactWithIff(_) => {
                FactResult::ForallFactWithIff(FactStmtResult::Success(success))
            }
            Fact::NotForall(_) => FactResult::NotForall(FactStmtResult::Success(success)),
        }
    }

    pub fn new_unknown(unknown: FactUnknown) -> Self {
        match &unknown {
            FactUnknown::AtomicFact(_) => {
                FactResult::AtomicFact(FactStmtResult::Unknown(Box::new(unknown)))
            }
            FactUnknown::ExistFact(_) => {
                FactResult::ExistFact(FactStmtResult::Unknown(Box::new(unknown)))
            }
            FactUnknown::OrFact(_) => {
                FactResult::OrFact(FactStmtResult::Unknown(Box::new(unknown)))
            }
            FactUnknown::AndFact(_) => {
                FactResult::AndFact(FactStmtResult::Unknown(Box::new(unknown)))
            }
            FactUnknown::ChainFact(_) => {
                FactResult::ChainFact(FactStmtResult::Unknown(Box::new(unknown)))
            }
            FactUnknown::ForallFact(_) => {
                FactResult::ForallFact(FactStmtResult::Unknown(Box::new(unknown)))
            }
            FactUnknown::ForallFactWithIff(_) => {
                FactResult::ForallFactWithIff(FactStmtResult::Unknown(Box::new(unknown)))
            }
            FactUnknown::NotForall(_) => {
                FactResult::NotForall(FactStmtResult::Unknown(Box::new(unknown)))
            }
        }
    }

    pub fn is_unknown(&self) -> bool {
        self.unknown().is_some()
    }

    pub fn success(&self) -> Option<&FactualStmtSuccess> {
        match self {
            FactResult::AtomicFact(result)
            | FactResult::ExistFact(result)
            | FactResult::OrFact(result)
            | FactResult::AndFact(result)
            | FactResult::ChainFact(result)
            | FactResult::ForallFact(result)
            | FactResult::ForallFactWithIff(result)
            | FactResult::NotForall(result) => result.success(),
        }
    }

    pub fn success_mut(&mut self) -> Option<&mut FactualStmtSuccess> {
        match self {
            FactResult::AtomicFact(result)
            | FactResult::ExistFact(result)
            | FactResult::OrFact(result)
            | FactResult::AndFact(result)
            | FactResult::ChainFact(result)
            | FactResult::ForallFact(result)
            | FactResult::ForallFactWithIff(result)
            | FactResult::NotForall(result) => result.success_mut(),
        }
    }

    pub fn unknown(&self) -> Option<&FactUnknown> {
        match self {
            FactResult::AtomicFact(result)
            | FactResult::ExistFact(result)
            | FactResult::OrFact(result)
            | FactResult::AndFact(result)
            | FactResult::ChainFact(result)
            | FactResult::ForallFact(result)
            | FactResult::ForallFactWithIff(result)
            | FactResult::NotForall(result) => result.unknown(),
        }
    }

    pub fn into_success(self) -> Option<FactualStmtSuccess> {
        match self {
            FactResult::AtomicFact(result)
            | FactResult::ExistFact(result)
            | FactResult::OrFact(result)
            | FactResult::AndFact(result)
            | FactResult::ChainFact(result)
            | FactResult::ForallFact(result)
            | FactResult::ForallFactWithIff(result)
            | FactResult::NotForall(result) => result.into_success(),
        }
    }

    pub fn into_unknown(self) -> Option<FactUnknown> {
        match self {
            FactResult::AtomicFact(result)
            | FactResult::ExistFact(result)
            | FactResult::OrFact(result)
            | FactResult::AndFact(result)
            | FactResult::ChainFact(result)
            | FactResult::ForallFact(result)
            | FactResult::ForallFactWithIff(result)
            | FactResult::NotForall(result) => result.into_unknown(),
        }
    }
}

impl FactStmtResult {
    pub fn success(&self) -> Option<&FactualStmtSuccess> {
        match self {
            FactStmtResult::Success(success) => Some(success),
            FactStmtResult::Unknown(_) => None,
        }
    }

    pub fn success_mut(&mut self) -> Option<&mut FactualStmtSuccess> {
        match self {
            FactStmtResult::Success(success) => Some(success),
            FactStmtResult::Unknown(_) => None,
        }
    }

    pub fn unknown(&self) -> Option<&FactUnknown> {
        match self {
            FactStmtResult::Success(_) => None,
            FactStmtResult::Unknown(unknown) => Some(unknown.as_ref()),
        }
    }

    pub fn into_success(self) -> Option<FactualStmtSuccess> {
        match self {
            FactStmtResult::Success(success) => Some(success),
            FactStmtResult::Unknown(_) => None,
        }
    }

    pub fn into_unknown(self) -> Option<FactUnknown> {
        match self {
            FactStmtResult::Success(_) => None,
            FactStmtResult::Unknown(unknown) => Some(*unknown),
        }
    }
}
