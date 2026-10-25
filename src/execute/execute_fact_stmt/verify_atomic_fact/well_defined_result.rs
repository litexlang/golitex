use crate::ast::fact::Fact;
use crate::ast::names::AtomicName;
use crate::execute::execute_fact_stmt::well_defined_results::{
    FailToVerifyObjWellDefinedResult, ObjWellDefinedProof,
};
use crate::execute::execute_fact_stmt::VerifyFactResult;

pub enum FailToVerifyAtomicFactWellDefinedResult {
    RealAnalysisDomain {
        fact: crate::ast::fact::AtomicFact,
        well_defined_of_each_parameter: Vec<ObjWellDefinedProof>,
    },
    FunctionLimitDomain {
        function: crate::ast::obj::Obj,
        well_defined_of_each_parameter: Vec<ObjWellDefinedProof>,
    },
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
    MultivariableAnalysis(MultivariableAnalysisPredicateDomainProof),
    SequenceAnalysis(SequenceAnalysisPredicateDomainProof),
    FunctionAnalysis(FunctionAnalysisPredicateDomainProof),
    FunctionLimit(FunctionLimitPredicateDomainProof),
    SequenceLimit(SequenceLimitPredicateDomainProof),
    ByKnownFact(super::AtomicExceptEqualityFactSearchProofByKnownAtomicFact),
    ByKnownZeroRemainder(
        Box<super::verify_atomic_except_equality::known_divisibility::KnownZeroRemainderProof>,
    ),
    ByRequirements(Vec<PredicateDomainWellDefinedProof>),
    ByCheckedArguments(Vec<PredicateDomainArgumentMembershipProof>),
}

// These memberships consume the enclosing atomic proof's checked argument WD.
// The index identifies that exact argument; no cache or duplicated WD is needed.
pub struct PredicateDomainArgumentMembershipProof {
    pub requirement: Fact,
    pub argument_index: usize,
    pub membership: super::structural_membership_proof::StructuralMembershipProof,
}

impl PredicateDomainArgumentMembershipProof {
    pub fn new(
        requirement: Fact,
        argument_index: usize,
        membership: super::structural_membership_proof::StructuralMembershipProof,
    ) -> Self {
        Self {
            requirement,
            argument_index,
            membership,
        }
    }
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

pub struct SequenceAnalysisPredicateDomainProof {
    pub sequence_source:
        Box<crate::execute::execute_fact_stmt::function_domain::CompleteFunctionDomainProof>,
}
pub struct FunctionAnalysisPredicateDomainProof {
    pub function_domain:
        crate::execute::execute_fact_stmt::function_limit::RealFunctionLimitDomainProof,
    pub requirements: Vec<PredicateDomainWellDefinedProof>,
}

pub struct SequenceLimitPredicateDomainProof {
    pub sequence_source:
        Box<crate::execute::execute_fact_stmt::function_domain::CompleteFunctionDomainProof>,
    pub value_real: super::structural_membership_proof::StructuralMembershipProof,
}

pub struct FunctionLimitPredicateDomainProof {
    pub function_domain:
        crate::execute::execute_fact_stmt::function_limit::RealFunctionLimitDomainProof,
    pub approach_real: FunctionLimitApproachRealProof,
    pub value_real: Box<VerifyFactResult>,
}

pub enum FunctionLimitApproachRealProof {
    Finite(Box<VerifyFactResult>),
    AtPositiveInfinity,
    AtNegativeInfinity,
}

pub struct MultivariableAnalysisPredicateDomainProof {
    pub function_domain:
        Box<crate::execute::execute_fact_stmt::function_domain::CompleteFunctionDomainProof>,
    pub requirements: Vec<PredicateDomainWellDefinedProof>,
}
