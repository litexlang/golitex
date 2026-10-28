use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::{
    AtomicFactWellDefinedProof, FailToVerifyAtomicFactWellDefinedResult,
};
use crate::result_detail::OutputDetail;
use crate::runtime::RuntimeResult;

pub struct FailToVerifyChainFactWellDefinedResult {
    pub fact: crate::ast::fact::ChainFact,
    pub failed_index: usize,
    pub succeeded_adjacent: Vec<AtomicFactWellDefinedProof>,
    pub failed_adjacent: FailToVerifyAtomicFactWellDefinedResult,
}

// Success-only evidence that every adjacent chain atomic is well-defined.
// Example: `1 < 2 < 3` needs WD of `1 < 2` and `2 < 3`.
pub enum ChainFactWellDefinedProof {
    Compact(CompactChainFactWellDefinedProof),
    Normal(NormalChainFactWellDefinedProof),
    Detailed(Box<DetailedChainFactWellDefinedProof>),
}

pub struct CompactChainFactWellDefinedProof {}
pub struct NormalChainFactWellDefinedProof {}
pub struct DetailedChainFactWellDefinedProof {
    pub adjacent: Vec<AtomicFactWellDefinedProof>,
}

impl ChainFactWellDefinedProof {
    pub fn new(detail: OutputDetail, capacity: usize) -> Self {
        match detail {
            OutputDetail::Compact => Self::Compact(CompactChainFactWellDefinedProof {}),
            OutputDetail::Normal => Self::Normal(NormalChainFactWellDefinedProof {}),
            OutputDetail::Detailed => Self::Detailed(Box::new(DetailedChainFactWellDefinedProof {
                adjacent: Vec::with_capacity(capacity),
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

    pub fn into_compact(self) -> RuntimeResult<CompactChainFactWellDefinedProof> {
        OutputDetail::Compact.require(self.detail(), "chain WD")?;
        match self {
            Self::Compact(proof) => Ok(proof),
            _ => unreachable!(),
        }
    }

    pub fn into_normal(self) -> RuntimeResult<NormalChainFactWellDefinedProof> {
        OutputDetail::Normal.require(self.detail(), "chain WD")?;
        match self {
            Self::Normal(proof) => Ok(proof),
            _ => unreachable!(),
        }
    }

    pub fn as_detailed(&self) -> RuntimeResult<&DetailedChainFactWellDefinedProof> {
        OutputDetail::Detailed.require(self.detail(), "chain WD")?;
        match self {
            Self::Detailed(proof) => Ok(proof),
            _ => unreachable!(),
        }
    }

    pub fn as_detailed_mut(&mut self) -> RuntimeResult<&mut DetailedChainFactWellDefinedProof> {
        OutputDetail::Detailed.require(self.detail(), "chain WD")?;
        match self {
            Self::Detailed(proof) => Ok(proof),
            _ => unreachable!(),
        }
    }

    pub(crate) fn push_adjacent(&mut self, proof: AtomicFactWellDefinedProof) -> RuntimeResult<()> {
        self.detail().require(proof.detail(), "chain WD adjacent")?;
        match self {
            Self::Compact(_) => {
                proof.into_compact()?;
            }
            Self::Normal(_) => {
                proof.into_normal()?;
            }
            Self::Detailed(parent) => parent.adjacent.push(proof),
        }
        Ok(())
    }

    pub(crate) fn into_completed(self) -> Vec<AtomicFactWellDefinedProof> {
        match self {
            Self::Compact(_) | Self::Normal(_) => Vec::new(),
            Self::Detailed(proof) => proof.adjacent,
        }
    }
}

// Soft miss vs success for chain-fact WD.
pub enum VerifyChainFactWellDefinedResult {
    Success(ChainFactWellDefinedProof),
    Failed(FailToVerifyChainFactWellDefinedResult),
}

impl VerifyChainFactWellDefinedResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}
