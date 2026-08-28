//! Successful fact verification outcomes and proof access.

use crate::prelude::*;
use std::fmt;

pub struct SuccessVerifyAtomicFactResult {
    pub statement: AtomicFact,
    pub proof: SuccessFactProofResult,
}

pub struct SuccessVerifyExistFactResult {
    pub statement: ExistFactEnum,
    pub proof: SuccessFactProofResult,
}

pub struct SuccessVerifyOrFactResult {
    pub statement: OrFact,
    pub proof: SuccessFactProofResult,
}

pub struct SuccessVerifyAndFactResult {
    pub statement: AndFact,
    pub proof: SuccessFactProofResult,
}

pub struct SuccessVerifyChainFactResult {
    pub statement: ChainFact,
    pub proof: SuccessFactProofResult,
}

pub struct SuccessVerifyForallFactResult {
    pub statement: ForallFact,
    pub proof: SuccessFactProofResult,
}

pub struct SuccessVerifyForallFactWithIffResult {
    pub statement: ForallFactWithIff,
    pub proof: SuccessFactProofResult,
}

pub struct SuccessVerifyNotForallFactResult {
    pub statement: NotForallFact,
    pub proof: SuccessFactProofResult,
}

/// Successful output of the `verify_fact` family. The variants follow the
/// same semantic split as `Fact`; each payload is a named result structure.
pub enum SuccessVerifyFactResult {
    AtomicFact(Box<SuccessVerifyAtomicFactResult>),
    ExistFact(Box<SuccessVerifyExistFactResult>),
    OrFact(Box<SuccessVerifyOrFactResult>),
    AndFact(Box<SuccessVerifyAndFactResult>),
    ChainFact(Box<SuccessVerifyChainFactResult>),
    ForallFact(Box<SuccessVerifyForallFactResult>),
    ForallFactWithIff(Box<SuccessVerifyForallFactWithIffResult>),
    NotForallFact(Box<SuccessVerifyNotForallFactResult>),
}

impl SuccessVerifyFactResult {
    pub fn new(statement: Fact, proof: SuccessFactProofResult) -> Self {
        match statement {
            Fact::AtomicFact(statement) => {
                Self::AtomicFact(Box::new(SuccessVerifyAtomicFactResult { statement, proof }))
            }
            Fact::ExistFact(statement) => {
                Self::ExistFact(Box::new(SuccessVerifyExistFactResult { statement, proof }))
            }
            Fact::OrFact(statement) => {
                Self::OrFact(Box::new(SuccessVerifyOrFactResult { statement, proof }))
            }
            Fact::AndFact(statement) => {
                Self::AndFact(Box::new(SuccessVerifyAndFactResult { statement, proof }))
            }
            Fact::ChainFact(statement) => {
                Self::ChainFact(Box::new(SuccessVerifyChainFactResult { statement, proof }))
            }
            Fact::ForallFact(statement) => {
                Self::ForallFact(Box::new(SuccessVerifyForallFactResult { statement, proof }))
            }
            Fact::ForallFactWithIff(statement) => {
                Self::ForallFactWithIff(Box::new(SuccessVerifyForallFactWithIffResult {
                    statement,
                    proof,
                }))
            }
            Fact::NotForall(statement) => {
                Self::NotForallFact(Box::new(SuccessVerifyNotForallFactResult {
                    statement,
                    proof,
                }))
            }
        }
    }

    pub fn fact(&self) -> Fact {
        match self {
            Self::AtomicFact(result) => result.statement.clone().into(),
            Self::ExistFact(result) => result.statement.clone().into(),
            Self::OrFact(result) => result.statement.clone().into(),
            Self::AndFact(result) => result.statement.clone().into(),
            Self::ChainFact(result) => result.statement.clone().into(),
            Self::ForallFact(result) => result.statement.clone().into(),
            Self::ForallFactWithIff(result) => result.statement.clone().into(),
            Self::NotForallFact(result) => result.statement.clone().into(),
        }
    }

    pub fn proof(&self) -> &SuccessFactProofResult {
        match self {
            Self::AtomicFact(result) => &result.proof,
            Self::ExistFact(result) => &result.proof,
            Self::OrFact(result) => &result.proof,
            Self::AndFact(result) => &result.proof,
            Self::ChainFact(result) => &result.proof,
            Self::ForallFact(result) => &result.proof,
            Self::ForallFactWithIff(result) => &result.proof,
            Self::NotForallFact(result) => &result.proof,
        }
    }

    pub fn proof_mut(&mut self) -> &mut SuccessFactProofResult {
        match self {
            Self::AtomicFact(result) => &mut result.proof,
            Self::ExistFact(result) => &mut result.proof,
            Self::OrFact(result) => &mut result.proof,
            Self::AndFact(result) => &mut result.proof,
            Self::ChainFact(result) => &mut result.proof,
            Self::ForallFact(result) => &mut result.proof,
            Self::ForallFactWithIff(result) => &mut result.proof,
            Self::NotForallFact(result) => &mut result.proof,
        }
    }

    pub fn is_verified_by_builtin_rules_only(&self) -> bool {
        self.proof().tree_is_builtin_rules_only()
    }

    pub fn into_parts(self) -> (Fact, SuccessFactProofResult) {
        match self {
            Self::AtomicFact(result) => (result.statement.into(), result.proof),
            Self::ExistFact(result) => (result.statement.into(), result.proof),
            Self::OrFact(result) => (result.statement.into(), result.proof),
            Self::AndFact(result) => (result.statement.into(), result.proof),
            Self::ChainFact(result) => (result.statement.into(), result.proof),
            Self::ForallFact(result) => (result.statement.into(), result.proof),
            Self::ForallFactWithIff(result) => (result.statement.into(), result.proof),
            Self::NotForallFact(result) => (result.statement.into(), result.proof),
        }
    }
}

impl fmt::Debug for SuccessVerifyFactResult {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("SuccessVerifyFactResult")
            .field("statement", &self.fact().to_string())
            .field("proof", self.proof())
            .finish()
    }
}
