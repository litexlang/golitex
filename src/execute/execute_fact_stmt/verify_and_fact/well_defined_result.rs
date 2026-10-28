use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::{
    AtomicFactWellDefinedProof, FailToVerifyAtomicFactWellDefinedResult,
};
use crate::result_detail::OutputDetail;
use crate::runtime::RuntimeResult;

pub struct FailToVerifyAndFactWellDefinedResult {
    pub fact: crate::ast::fact::AndFact,
    pub failed_index: usize,
    pub succeeded_components: Vec<AtomicFactWellDefinedProof>,
    pub failed_component: FailToVerifyAtomicFactWellDefinedResult,
}

// Success-only evidence that every and-conjunct is well-defined.
// Example: `1 < 2 and 2 < 3` needs WD of both atomics.
pub enum AndFactWellDefinedProof {
    Compact(CompactAndFactWellDefinedProof),
    Normal(NormalAndFactWellDefinedProof),
    Detailed(Box<DetailedAndFactWellDefinedProof>),
}

pub struct CompactAndFactWellDefinedProof {}
pub struct NormalAndFactWellDefinedProof {}
pub struct DetailedAndFactWellDefinedProof {
    pub components: Vec<AtomicFactWellDefinedProof>,
}

impl AndFactWellDefinedProof {
    pub fn new(detail: OutputDetail, capacity: usize) -> Self {
        match detail {
            OutputDetail::Compact => Self::Compact(CompactAndFactWellDefinedProof {}),
            OutputDetail::Normal => Self::Normal(NormalAndFactWellDefinedProof {}),
            OutputDetail::Detailed => Self::Detailed(Box::new(DetailedAndFactWellDefinedProof {
                components: Vec::with_capacity(capacity),
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

    pub fn into_compact(self) -> RuntimeResult<CompactAndFactWellDefinedProof> {
        OutputDetail::Compact.require(self.detail(), "and WD")?;
        match self {
            Self::Compact(proof) => Ok(proof),
            _ => unreachable!(),
        }
    }

    pub fn into_normal(self) -> RuntimeResult<NormalAndFactWellDefinedProof> {
        OutputDetail::Normal.require(self.detail(), "and WD")?;
        match self {
            Self::Normal(proof) => Ok(proof),
            _ => unreachable!(),
        }
    }

    pub fn as_detailed(&self) -> RuntimeResult<&DetailedAndFactWellDefinedProof> {
        OutputDetail::Detailed.require(self.detail(), "and WD")?;
        match self {
            Self::Detailed(proof) => Ok(proof),
            _ => unreachable!(),
        }
    }

    pub fn as_detailed_mut(&mut self) -> RuntimeResult<&mut DetailedAndFactWellDefinedProof> {
        OutputDetail::Detailed.require(self.detail(), "and WD")?;
        match self {
            Self::Detailed(proof) => Ok(proof),
            _ => unreachable!(),
        }
    }

    pub(crate) fn push_component(
        &mut self,
        proof: AtomicFactWellDefinedProof,
    ) -> RuntimeResult<()> {
        self.detail().require(proof.detail(), "and WD component")?;
        match self {
            Self::Compact(_) => {
                proof.into_compact()?;
            }
            Self::Normal(_) => {
                proof.into_normal()?;
            }
            Self::Detailed(parent) => parent.components.push(proof),
        }
        Ok(())
    }

    pub(crate) fn into_completed(self) -> Vec<AtomicFactWellDefinedProof> {
        match self {
            Self::Compact(_) | Self::Normal(_) => Vec::new(),
            Self::Detailed(proof) => proof.components,
        }
    }
}

// Soft miss vs success for and-fact WD.
pub enum VerifyAndFactWellDefinedResult {
    Success(AndFactWellDefinedProof),
    Failed(FailToVerifyAndFactWellDefinedResult),
}

impl VerifyAndFactWellDefinedResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}
