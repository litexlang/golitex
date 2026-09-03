//! Transparent and checked-function definition reduction evidence.

use crate::prelude::*;
use std::fmt;
use std::rc::Rc;

/// One exact `let` definition consumed by a transparent fact reduction.
#[derive(Clone)]
pub struct TransparentDefinitionReductionUse {
    pub symbol: SymbolRef,
    pub definition_object: Obj,
    pub defining_equality: EqualFact,
    pub defining_equality_fact_id: FactId,
}

impl fmt::Debug for TransparentDefinitionReductionUse {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("TransparentDefinitionReductionUse")
            .field("symbol", &self.symbol)
            .field("definition_object", &self.definition_object.to_string())
            .field("defining_equality", &self.defining_equality.to_string())
            .field("defining_equality_fact_id", &self.defining_equality_fact_id)
            .finish()
    }
}

#[derive(Clone, Debug)]
pub struct TransparentDefinitionReductionEvidence {
    /// Deterministic `SymbolId` order. All substitutions form one nonrecursive
    /// pass from the source goal to the fact proved by the child Result.
    pub definitions: Vec<TransparentDefinitionReductionUse>,
}

impl TransparentDefinitionReductionEvidence {
    pub fn new(definitions: Vec<TransparentDefinitionReductionUse>) -> Self {
        Self { definitions }
    }
}

/// One target-directed fact transformation. The enclosing
/// `SuccessFactProofNode` owns the target proposition; this node owns the
/// immediately preceding successful fact result and the exact rule used for
/// the single transformation layer.
#[derive(Debug)]
pub struct SuccessTransformFactResult {
    pub rule: FactTransformationRule,
    pub source: Rc<SuccessFactProofNode>,
}

impl SuccessTransformFactResult {
    pub fn new(rule: FactTransformationRule, source: SuccessFactProofNode) -> Self {
        Self {
            rule,
            source: Rc::new(source),
        }
    }

    pub fn from_shared(rule: FactTransformationRule, source: Rc<SuccessFactProofNode>) -> Self {
        Self { rule, source }
    }
}

#[derive(Clone, Debug)]
pub struct SuccessStoredFactCitationProofResult {
    pub detail: Option<String>,
    pub source_fact: Fact,
    pub source_fact_id: FactId,
}

pub struct SuccessDefinitionReductionFactProofResult {
    pub detail: Option<String>,
    pub definition: DefPropStmt,
    pub verification: Rc<DefinitionReductionVerificationEvidence>,
}

impl fmt::Debug for SuccessDefinitionReductionFactProofResult {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        formatter
            .debug_struct("SuccessDefinitionReductionFactProofResult")
            .field("detail", &self.detail)
            .field("definition", &self.definition.to_string())
            .field("verification", &self.verification)
            .finish()
    }
}

#[derive(Debug)]
pub struct SuccessCheckedFunctionDefinitionReductionFactProofResult {
    pub detail: Option<String>,
    pub verification: CheckedFunctionDefinitionReductionEvidence,
}

#[derive(Clone, Debug)]
pub struct SuccessDiagnosticFactProofResult {
    pub detail: String,
}

#[derive(Debug)]
pub struct DefinitionReductionVerificationEvidence {
    pub argument_verification: SuccessVerifyArgsSatisfyParamDefResult,
    pub clause_facts: Vec<Fact>,
    pub clause_checks: Vec<VerifyFactResult>,
}

pub struct CheckedFunctionDefinitionReductionEvidence {
    pub definition_object: Obj,
    pub defining_equality: Fact,
    pub defining_equality_fact_id: FactId,
    pub application_side: Obj,
    pub reduced: Obj,
    pub other_side: Obj,
    pub application_is_left: bool,
    /// Complete proof of `reduced = other_side`. The outer node composes this
    /// child with the exact checked unfolding identified above.
    pub reduced_equality: VerifyFactResult,
}

impl fmt::Debug for CheckedFunctionDefinitionReductionEvidence {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        formatter
            .debug_struct("CheckedFunctionDefinitionReductionEvidence")
            .field("definition_object", &self.definition_object.to_string())
            .field("defining_equality", &self.defining_equality.to_string())
            .field("defining_equality_fact_id", &self.defining_equality_fact_id)
            .field("application_side", &self.application_side.to_string())
            .field("reduced", &self.reduced.to_string())
            .field("other_side", &self.other_side.to_string())
            .field("application_is_left", &self.application_is_left)
            .field("reduced_equality", &self.reduced_equality)
            .finish()
    }
}
