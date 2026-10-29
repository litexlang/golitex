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
        fact: crate::ast::fact::AtomicFact,
        function: crate::ast::obj::Obj,
        well_defined_of_each_parameter: Vec<ObjWellDefinedProof>,
    },
    Argument {
        fact: crate::ast::fact::AtomicFact,
        reason: FailToVerifyObjWellDefinedResult,
    },
    Predicate {
        fact: crate::ast::fact::AtomicFact,
        well_defined_of_each_parameter: Vec<ObjWellDefinedProof>,
        reason: PredicateSignatureWellDefinedFailure,
    },
    Domain {
        fact: crate::ast::fact::AtomicFact,
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
pub enum AtomicFactWellDefinedProof {
    Compact(CompactAtomicFactWellDefinedProof),
    Normal(NormalAtomicFactWellDefinedProof),
    Detailed(Box<DetailedAtomicFactWellDefinedProof>),
}
pub struct CompactAtomicFactWellDefinedProof {}
pub struct NormalAtomicFactWellDefinedProof {}
pub struct DetailedAtomicFactWellDefinedProof {
    pub well_defined_of_each_parameter: Vec<ObjWellDefinedProof>,
    pub predicate_signature: PredicateSignatureWellDefinedProof,
    pub predicate_domain: PredicateDomainProof,
}

impl AtomicFactWellDefinedProof {
    pub fn new(
        detail: crate::result_detail::OutputDetail,
        build: impl FnOnce() -> DetailedAtomicFactWellDefinedProof,
    ) -> crate::runtime::RuntimeResult<Self> {
        use crate::result_detail::OutputDetail;
        Ok(match detail {
            OutputDetail::Compact => Self::Compact(CompactAtomicFactWellDefinedProof {}),
            OutputDetail::Normal => Self::Normal(NormalAtomicFactWellDefinedProof {}),
            OutputDetail::Detailed => {
                let proof = build();
                for child in &proof.well_defined_of_each_parameter {
                    detail.require(child.detail(), "atomic WD child")?;
                }
                Self::Detailed(Box::new(proof))
            }
        })
    }
    pub fn detail(&self) -> crate::result_detail::OutputDetail {
        use crate::result_detail::OutputDetail;
        match self {
            Self::Compact(_) => OutputDetail::Compact,
            Self::Normal(_) => OutputDetail::Normal,
            Self::Detailed(_) => OutputDetail::Detailed,
        }
    }
    pub fn into_normal(self) -> crate::runtime::RuntimeResult<NormalAtomicFactWellDefinedProof> {
        crate::result_detail::OutputDetail::Normal.require(self.detail(), "atomic WD")?;
        match self {
            Self::Normal(proof) => Ok(proof),
            _ => unreachable!(),
        }
    }
    pub fn into_compact(self) -> crate::runtime::RuntimeResult<CompactAtomicFactWellDefinedProof> {
        crate::result_detail::OutputDetail::Compact.require(self.detail(), "atomic WD")?;
        match self {
            Self::Compact(proof) => Ok(proof),
            _ => unreachable!(),
        }
    }
    pub fn as_detailed(
        &self,
    ) -> crate::runtime::RuntimeResult<&DetailedAtomicFactWellDefinedProof> {
        crate::result_detail::OutputDetail::Detailed.require(self.detail(), "atomic WD")?;
        match self {
            Self::Detailed(proof) => Ok(proof),
            _ => unreachable!(),
        }
    }
    pub fn as_detailed_mut(
        &mut self,
    ) -> crate::runtime::RuntimeResult<&mut DetailedAtomicFactWellDefinedProof> {
        crate::result_detail::OutputDetail::Detailed.require(self.detail(), "atomic WD")?;
        match self {
            Self::Detailed(proof) => Ok(proof),
            _ => unreachable!(),
        }
    }
    pub(crate) fn detailed_ref(&self) -> &DetailedAtomicFactWellDefinedProof {
        self.as_detailed().unwrap_or_else(|error| panic!("{error}"))
    }
}

impl FailToVerifyAtomicFactWellDefinedResult {
    pub fn fact(&self) -> &crate::ast::fact::AtomicFact {
        match self {
            Self::RealAnalysisDomain { fact, .. }
            | Self::FunctionLimitDomain { fact, .. }
            | Self::Argument { fact, .. }
            | Self::Predicate { fact, .. }
            | Self::Domain { fact, .. } => fact,
        }
    }
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
    pub result: PredicateDomainRequirementProof,
}

pub enum PredicateDomainRequirementProof {
    Verified(Box<VerifyFactResult>),
    CheckedArgument(PredicateDomainArgumentMembershipProof),
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
