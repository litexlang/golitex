//! Choice-principle proof outcomes and obligations.

use crate::prelude::*;
use std::fmt;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SuccessVerifyByChoiceProofKind {
    AxiomOfChoice,
    ZornLemma,
    RegularityAxiom,
}

pub enum SuccessVerifyByChoiceTargetResult {
    AxiomOfChoice {
        family: Obj,
    },
    ZornLemma {
        set: Obj,
        relation: AtomicName,
        upper_bound: AtomicName,
        maximal: AtomicName,
    },
    RegularityAxiom {
        set: Obj,
    },
}

impl fmt::Debug for SuccessVerifyByChoiceTargetResult {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::AxiomOfChoice { family } => formatter
                .debug_struct("AxiomOfChoice")
                .field("family", &family.to_string())
                .finish(),
            Self::ZornLemma {
                set,
                relation,
                upper_bound,
                maximal,
            } => formatter
                .debug_struct("ZornLemma")
                .field("set", &set.to_string())
                .field("relation", &relation.to_string())
                .field("upper_bound", &upper_bound.to_string())
                .field("maximal", &maximal.to_string())
                .finish(),
            Self::RegularityAxiom { set } => formatter
                .debug_struct("RegularityAxiom")
                .field("set", &set.to_string())
                .finish(),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SuccessVerifyByChoiceObligationRole {
    ChoiceFamilyIsSet,
    ChoiceMembersNonempty,
    ZornNonempty,
    ZornReflexive,
    ZornTransitive,
    ZornAntisymmetric,
    ZornChainUpperBound,
    RegularityNonempty,
}

#[derive(Debug)]
pub struct SuccessVerifyByChoiceResult {
    pub proof_kind: SuccessVerifyByChoiceProofKind,
    pub target: SuccessVerifyByChoiceTargetResult,
    pub proof_steps: Vec<StmtResult>,
    pub obligations: Vec<SuccessVerifyByChoiceObligationResult>,
    pub trusted_conclusion: Fact,
    pub trusted_conclusion_fact_id: FactId,
}

#[derive(Debug)]
pub struct SuccessVerifyByChoiceObligationResult {
    pub role: SuccessVerifyByChoiceObligationRole,
    pub fact: Fact,
    pub fact_id: FactId,
    pub check: Option<Box<StmtResult>>,
}

impl SuccessVerifyByChoiceResult {
    pub fn new(
        proof_kind: SuccessVerifyByChoiceProofKind,
        target: SuccessVerifyByChoiceTargetResult,
        proof_steps: Vec<StmtResult>,
        obligations: Vec<SuccessVerifyByChoiceObligationResult>,
        trusted_conclusion: Fact,
        trusted_conclusion_fact_id: FactId,
    ) -> Self {
        SuccessVerifyByChoiceResult {
            proof_kind,
            target,
            proof_steps,
            obligations,
            trusted_conclusion,
            trusted_conclusion_fact_id,
        }
    }
}
