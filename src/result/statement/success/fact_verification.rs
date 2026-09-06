//! Successful fact verification outcomes and proof access.

use crate::prelude::*;
use std::fmt;
use std::rc::Rc;

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
pub enum SuccessFactProofNode {
    AtomicFact(Box<SuccessVerifyAtomicFactResult>),
    ExistFact(Box<SuccessVerifyExistFactResult>),
    OrFact(Box<SuccessVerifyOrFactResult>),
    AndFact(Box<SuccessVerifyAndFactResult>),
    ChainFact(Box<SuccessVerifyChainFactResult>),
    ForallFact(Box<SuccessVerifyForallFactResult>),
    ForallFactWithIff(Box<SuccessVerifyForallFactWithIffResult>),
    NotForallFact(Box<SuccessVerifyNotForallFactResult>),
}

impl SuccessFactProofNode {
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

impl fmt::Debug for SuccessFactProofNode {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("SuccessFactProofNode")
            .field("statement", &self.fact().to_string())
            .field("proof", self.proof())
            .finish()
    }
}

/// A successful fact verification owns both phases: the complete
/// well-definedness derivation and the proof of the proposition itself.
pub struct VerifiedFactResult {
    pub checked: WellDefinedFactResult,
    pub verification: Rc<SuccessFactProofNode>,
}

impl VerifiedFactResult {
    #[track_caller]
    pub fn new(checked: WellDefinedFactResult, verification: Rc<SuccessFactProofNode>) -> Self {
        let checked_fact = checked.fact.to_string();
        let verification_fact = verification.fact().to_string();
        if checked_fact != verification_fact {
            eprintln!(
                "mismatched verified fact at {}: checked=`{checked_fact}`, proof=`{verification_fact}`",
                std::panic::Location::caller()
            );
        }
        assert_eq!(
            checked_fact, verification_fact,
            "fact WD and truth proof must describe the same resolved proposition"
        );
        Self {
            checked,
            verification,
        }
    }

    pub fn fact(&self) -> Fact {
        self.checked.fact.clone()
    }

    pub fn proof(&self) -> &SuccessFactProofResult {
        self.verification.proof()
    }

    pub fn proof_mut(&mut self) -> &mut SuccessFactProofResult {
        self.try_proof_mut()
            .expect("a shared proof DAG node cannot be mutated in place")
    }

    pub fn try_proof_mut(&mut self) -> Option<&mut SuccessFactProofResult> {
        Rc::get_mut(&mut self.verification).map(SuccessFactProofNode::proof_mut)
    }

    pub fn is_verified_by_builtin_rules_only(&self) -> bool {
        self.proof().tree_is_builtin_rules_only()
    }
}

impl fmt::Debug for VerifiedFactResult {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("VerifiedFactResult")
            .field("fact", &self.checked.fact.to_string())
            .field("well_definedness", &self.checked.proof)
            .field("proof", self.proof())
            .finish()
    }
}

#[derive(Debug)]
pub struct UnknownVerifyFactResult {
    pub checked: WellDefinedFactResult,
    pub unknown: UnknownFactResult,
}

#[derive(Debug)]
pub enum VerifyFactResult {
    Verified(Rc<VerifiedFactResult>),
    Unknown(Box<UnknownVerifyFactResult>),
}

impl VerifyFactResult {
    pub fn fact(&self) -> Fact {
        self.checked().fact.clone()
    }

    pub fn line_file(&self) -> LineFile {
        self.fact().line_file()
    }

    pub fn is_verified(&self) -> bool {
        matches!(self, Self::Verified(_))
    }

    pub fn is_success(&self) -> bool {
        self.is_verified()
    }

    pub fn is_unknown(&self) -> bool {
        matches!(self, Self::Unknown(_))
    }

    pub fn verified(&self) -> Option<&Rc<VerifiedFactResult>> {
        match self {
            Self::Verified(result) => Some(result),
            Self::Unknown(_) => None,
        }
    }

    pub fn verified_mut(&mut self) -> Option<&mut VerifiedFactResult> {
        match self {
            Self::Verified(result) => Rc::get_mut(result),
            Self::Unknown(_) => None,
        }
    }

    pub fn into_verified(self) -> Option<Rc<VerifiedFactResult>> {
        match self {
            Self::Verified(result) => Some(result),
            Self::Unknown(_) => None,
        }
    }

    pub fn unknown(&self) -> Option<&UnknownVerifyFactResult> {
        match self {
            Self::Verified(_) => None,
            Self::Unknown(result) => Some(result),
        }
    }

    pub fn checked(&self) -> &WellDefinedFactResult {
        match self {
            Self::Verified(result) => &result.checked,
            Self::Unknown(result) => &result.checked,
        }
    }

    pub fn proof(&self) -> Option<&SuccessFactProofResult> {
        self.verified().map(|result| result.proof())
    }

    pub fn as_fact_unknown(&self) -> Option<&UnknownFactResult> {
        self.unknown().map(|result| &result.unknown)
    }

    /// Verification nodes are process-local evidence, never stored facts.
    pub fn fact_id(&self) -> Option<FactId> {
        None
    }
}
