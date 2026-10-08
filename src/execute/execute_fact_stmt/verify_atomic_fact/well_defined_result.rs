use crate::ast::fact::Fact;
use crate::ast::names::AtomicName;
use crate::execute::execute_fact_stmt::well_defined_results::{
    FailToVerifyObjWellDefinedResult, ObjWellDefinedProof,
};
use crate::execute::execute_fact_stmt::VerifyFactResult;

pub enum FailToVerifyAtomicFactWellDefinedResult {
    Argument(FailToVerifyObjWellDefinedResult),
    Predicate {
        well_defined_of_each_parameter: Vec<ObjWellDefinedProof>,
        reason: PredicateSignatureWellDefinedFailure,
    },
    Domain {
        well_defined_of_each_parameter: Vec<ObjWellDefinedProof>,
        predicate_signature: PredicateSignatureWellDefinedProof,
        completed: Vec<PredicateDomainWellDefinedProof>,
        requirement: Fact,
        result: Box<VerifyFactResult>,
    },
}

pub enum PredicateSignatureWellDefinedFailure {
    Undefined {
        predicate: AtomicName,
    },
    Retired {
        predicate: AtomicName,
    },
    Arity {
        predicate: AtomicName,
        expected: usize,
        actual: usize,
    },
}

// Builtin arity is fixed by the AST leaf. User signatures are resolved using
// the full owner-qualified name, never only its local spelling.
pub enum PredicateSignatureWellDefinedProof {
    Builtin,
    Prop { predicate: AtomicName, arity: usize },
    AbstractProp { predicate: AtomicName, arity: usize },
}

// Success evidence follows the WD stages: argument objects, then signature.
pub struct AtomicFactWellDefinedProof {
    pub well_defined_of_each_parameter: Vec<ObjWellDefinedProof>,
    pub predicate_signature: PredicateSignatureWellDefinedProof,
    pub predicate_domain: PredicateDomainProof,
}

// Reusing a checked proposition also reuses its predicate-domain evidence.
// Arguments and the visible signature are still checked before this dispatch.
pub enum PredicateDomainProof {
    ByKnownFact(super::AtomicExceptEqualityFactSearchProofByKnownAtomicFact),
    ByRequirements(Vec<PredicateDomainWellDefinedProof>),
}

pub struct PredicateDomainWellDefinedProof {
    pub requirement: Fact,
    pub result: Box<VerifyFactResult>,
}

// Soft miss vs success for atomic-fact WD. Proof never embeds Fail.
pub enum VerifyAtomicFactWellDefinedResult {
    Success(AtomicFactWellDefinedProof),
    Failed(FailToVerifyAtomicFactWellDefinedResult),
}

impl VerifyAtomicFactWellDefinedResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}
