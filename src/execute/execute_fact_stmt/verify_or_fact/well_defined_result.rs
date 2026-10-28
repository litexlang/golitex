use crate::execute::execute_fact_stmt::well_defined_results::{
    FactWellDefinedProof, FailToVerifyFactWellDefinedResult,
};
use crate::result_detail::OutputDetail;
use crate::runtime::RuntimeResult;

pub struct FailToVerifyOrFactWellDefinedResult {
    pub fact: crate::ast::fact::OrFact,
    pub failed_index: usize,
    pub succeeded_branches: Vec<FactWellDefinedProof>,
    pub failed_branch: Box<FailToVerifyFactWellDefinedResult>,
}

// Well-definedness of an or-fact: WD each AndChainAtomic branch.
//
// Same contract as AtomicFactWellDefinedProof /
// VerifyAtomicFactWellDefinedResult: Proof is success-only;
// Result = Success(Proof) | Failed(reason).
//
// Example: `1 = 1 or 1 = 2` needs WD of both `1 = 1` and `1 = 2`.
// Example fail: `1 / 0 = 1 or 1 = 1` fails on the first branch.

// Success-only evidence that every or-branch is well-defined.
// Constructed only under Success; never embeds soft-fail.
pub enum OrFactWellDefinedProof {
    Compact(CompactOrFactWellDefinedProof),
    Normal(NormalOrFactWellDefinedProof),
    Detailed(Box<DetailedOrFactWellDefinedProof>),
}

pub struct CompactOrFactWellDefinedProof {}
pub struct NormalOrFactWellDefinedProof {}
pub struct DetailedOrFactWellDefinedProof {
    pub branches: Vec<FactWellDefinedProof>,
}

impl OrFactWellDefinedProof {
    pub fn new(detail: OutputDetail, capacity: usize) -> Self {
        match detail {
            OutputDetail::Compact => Self::Compact(CompactOrFactWellDefinedProof {}),
            OutputDetail::Normal => Self::Normal(NormalOrFactWellDefinedProof {}),
            OutputDetail::Detailed => Self::Detailed(Box::new(DetailedOrFactWellDefinedProof {
                branches: Vec::with_capacity(capacity),
            })),
        }
    }

    pub fn detail(&self) -> OutputDetail {
        match self {
            Self::Compact(_) => OutputDetail::Compact,
            Self::Normal(_) => OutputDetail::Normal,
            Self::Detailed(_) => OutputDetail::Detailed,
        }
    }

    pub fn into_compact(self) -> RuntimeResult<CompactOrFactWellDefinedProof> {
        OutputDetail::Compact.require(self.detail(), "or WD")?;
        match self {
            Self::Compact(proof) => Ok(proof),
            _ => unreachable!(),
        }
    }

    pub fn into_normal(self) -> RuntimeResult<NormalOrFactWellDefinedProof> {
        OutputDetail::Normal.require(self.detail(), "or WD")?;
        match self {
            Self::Normal(proof) => Ok(proof),
            _ => unreachable!(),
        }
    }

    pub fn as_detailed(&self) -> RuntimeResult<&DetailedOrFactWellDefinedProof> {
        OutputDetail::Detailed.require(self.detail(), "or WD")?;
        match self {
            Self::Detailed(proof) => Ok(proof),
            _ => unreachable!(),
        }
    }

    pub fn as_detailed_mut(&mut self) -> RuntimeResult<&mut DetailedOrFactWellDefinedProof> {
        OutputDetail::Detailed.require(self.detail(), "or WD")?;
        match self {
            Self::Detailed(proof) => Ok(proof),
            _ => unreachable!(),
        }
    }

    pub(crate) fn detailed_ref(&self) -> &DetailedOrFactWellDefinedProof {
        self.as_detailed().unwrap_or_else(|error| panic!("{error}"))
    }

    pub(crate) fn push_branch(&mut self, proof: FactWellDefinedProof) -> RuntimeResult<()> {
        proof.require_detail(self.detail(), "or WD branch")?;
        if let Self::Detailed(parent) = self {
            parent.branches.push(proof);
        }
        Ok(())
    }

    pub(crate) fn into_completed(self) -> Vec<FactWellDefinedProof> {
        match self {
            Self::Compact(_) | Self::Normal(_) => Vec::new(),
            Self::Detailed(proof) => proof.branches,
        }
    }
}

// Soft miss vs success for or-fact WD.
pub enum VerifyOrFactWellDefinedResult {
    Success(OrFactWellDefinedProof),
    Failed(FailToVerifyOrFactWellDefinedResult),
}

impl VerifyOrFactWellDefinedResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}
