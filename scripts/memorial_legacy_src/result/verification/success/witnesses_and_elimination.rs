//! Witness and existential-elimination outcomes.

use crate::prelude::*;
use std::fmt;

#[derive(Debug)]
pub struct SuccessVerifyWitnessExistResult {
    pub proof_steps: Vec<StmtResult>,
    /// One factual type-check result for every witness value that contributes
    /// a target-side existential requirement.  Plain `set` binders need no
    /// separate target proposition because every value already has type
    /// `LitexSet`.
    pub parameter_checks: Vec<Option<Box<VerifyFactResult>>>,
    /// One factual result for every direct existential body fact.
    pub body_checks: Vec<VerifyFactResult>,
    /// The final result for the uniqueness obligation, when the source form
    /// is `exist!`.
    pub uniqueness_check: Option<Box<VerifyFactResult>>,
}

pub struct SuccessVerifyWitnessAtomicFactResult {
    pub definition: DefPropStmt,
    pub instantiated_existential: ExistFact,
    pub definition_parameter_verification: Box<SuccessVerifyArgsSatisfyParamDefResult>,
    pub witness_verification: SuccessVerifyWitnessExistResult,
}

impl SuccessVerifyWitnessAtomicFactResult {
    pub fn new(
        definition: DefPropStmt,
        instantiated_existential: ExistFact,
        definition_parameter_verification: SuccessVerifyArgsSatisfyParamDefResult,
        witness_verification: SuccessVerifyWitnessExistResult,
    ) -> Self {
        SuccessVerifyWitnessAtomicFactResult {
            definition,
            instantiated_existential,
            definition_parameter_verification: Box::new(definition_parameter_verification),
            witness_verification,
        }
    }
}

impl fmt::Debug for SuccessVerifyWitnessAtomicFactResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("SuccessVerifyWitnessAtomicFactResult")
            .field("definition", &self.definition.name)
            .field(
                "instantiated_existential",
                &self.instantiated_existential.to_string(),
            )
            .field(
                "definition_parameter_verification",
                &self.definition_parameter_verification,
            )
            .field("witness_verification", &self.witness_verification)
            .finish()
    }
}

impl SuccessVerifyWitnessExistResult {
    pub fn new(
        proof_steps: Vec<StmtResult>,
        parameter_checks: Vec<Option<Box<VerifyFactResult>>>,
        body_checks: Vec<VerifyFactResult>,
        uniqueness_check: Option<VerifyFactResult>,
    ) -> Self {
        Self {
            proof_steps,
            parameter_checks,
            body_checks,
            uniqueness_check: uniqueness_check.map(Box::new),
        }
    }
}

pub struct SuccessVerifyExistentialEliminationResult {
    /// Checked existential/projection or scoped theorem application whose
    /// exact direct conclusion is retained recursively.
    pub source_result: ExistentialEliminationSourceResult,
    /// Exact existential eliminated after any definition projection.
    pub source_exist_fact: ExistFact,
    /// Exact instantiated type fact stored for every introduced witness.
    pub witness_type_facts: Vec<Fact>,
    /// Exact instantiated direct body facts stored by elimination.
    pub instantiated_body_facts: Vec<Fact>,
    /// `exist!` additionally stores a generated uniqueness theorem.  The
    /// current compiler tranche rejects that extra projection explicitly.
    pub includes_uniqueness: bool,
}

#[derive(Debug)]
pub enum ExistentialEliminationSourceResult {
    Fact(Box<VerifyFactResult>),
    TheoremApplication(Box<StmtResult>),
}

impl ExistentialEliminationSourceResult {
    pub fn fact(&self) -> Option<&VerifyFactResult> {
        match self {
            Self::Fact(result) => Some(result.as_ref()),
            Self::TheoremApplication(_) => None,
        }
    }

    pub fn theorem_application(&self) -> Option<&StmtResult> {
        match self {
            Self::Fact(_) => None,
            Self::TheoremApplication(result) => Some(result.as_ref()),
        }
    }
}

impl fmt::Debug for SuccessVerifyExistentialEliminationResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("SuccessVerifyExistentialEliminationResult")
            .field("source_result", &self.source_result)
            .field("source_exist_fact", &self.source_exist_fact.to_string())
            .field("witness_type_facts", &self.witness_type_facts)
            .field("instantiated_body_facts", &self.instantiated_body_facts)
            .field("includes_uniqueness", &self.includes_uniqueness)
            .finish()
    }
}

impl SuccessVerifyExistentialEliminationResult {
    pub fn new(
        source_result: ExistentialEliminationSourceResult,
        source_exist_fact: ExistFact,
        witness_type_facts: Vec<Fact>,
        instantiated_body_facts: Vec<Fact>,
        includes_uniqueness: bool,
    ) -> Self {
        Self {
            source_result,
            source_exist_fact,
            witness_type_facts,
            instantiated_body_facts,
            includes_uniqueness,
        }
    }
}
