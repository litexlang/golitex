//! Computational matching outputs retain their capture mode until checked extraction.
use super::verify_equality::result::ForallConclusionArgMatchProof;
use crate::ast::obj::Obj;
use crate::result_detail::OutputDetail;
use crate::runtime::{IdentifierId, RuntimeResult};
use std::collections::HashMap;

pub enum MatchForallConclusionArgsProof {
    Compact(CompactMatchForallConclusionArgsProof),
    Normal(NormalMatchForallConclusionArgsProof),
    Detailed(DetailedMatchForallConclusionArgsProof),
}
pub struct CompactMatchForallConclusionArgsProof {
    pub substitution: HashMap<IdentifierId, Obj>,
}
pub struct NormalMatchForallConclusionArgsProof {
    pub substitution: HashMap<IdentifierId, Obj>,
}
pub struct DetailedMatchForallConclusionArgsProof {
    pub substitution: HashMap<IdentifierId, Obj>,
    pub forall_parameters_match_what_args: Vec<Obj>,
    pub arg_match_proofs: Vec<ForallConclusionArgMatchProof>,
}
impl MatchForallConclusionArgsProof {
    pub fn detail(&self) -> OutputDetail {
        match self {
            Self::Compact(_) => OutputDetail::Compact,
            Self::Normal(_) => OutputDetail::Normal,
            Self::Detailed(_) => OutputDetail::Detailed,
        }
    }
    pub(crate) fn new(
        detail: OutputDetail,
        substitution: HashMap<IdentifierId, Obj>,
        forall_parameters_match_what_args: Vec<Obj>,
        arg_match_proofs: Vec<ForallConclusionArgMatchProof>,
    ) -> RuntimeResult<Self> {
        for child in &arg_match_proofs {
            detail.require(child.detail(), "ordered forall matching child")?;
        }
        Ok(match detail {
            OutputDetail::Compact => {
                Self::Compact(CompactMatchForallConclusionArgsProof { substitution })
            }
            OutputDetail::Normal => {
                Self::Normal(NormalMatchForallConclusionArgsProof { substitution })
            }
            OutputDetail::Detailed => Self::Detailed(DetailedMatchForallConclusionArgsProof {
                substitution,
                forall_parameters_match_what_args,
                arg_match_proofs,
            }),
        })
    }
    pub(crate) fn into_parts(
        self,
        expected: OutputDetail,
    ) -> RuntimeResult<(
        HashMap<IdentifierId, Obj>,
        Vec<Obj>,
        Vec<ForallConclusionArgMatchProof>,
    )> {
        expected.require(self.detail(), "ordered forall matching")?;
        Ok(match self {
            Self::Compact(proof) => (proof.substitution, Vec::new(), Vec::new()),
            Self::Normal(proof) => (proof.substitution, Vec::new(), Vec::new()),
            Self::Detailed(proof) => (
                proof.substitution,
                proof.forall_parameters_match_what_args,
                proof.arg_match_proofs,
            ),
        })
    }
}

pub enum PartialMatchForallConclusionArgsProof {
    Compact(CompactPartialMatchForallConclusionArgsProof),
    Normal(NormalPartialMatchForallConclusionArgsProof),
    Detailed(DetailedPartialMatchForallConclusionArgsProof),
}
pub struct CompactPartialMatchForallConclusionArgsProof {
    pub substitution: HashMap<IdentifierId, Obj>,
}
pub struct NormalPartialMatchForallConclusionArgsProof {
    pub substitution: HashMap<IdentifierId, Obj>,
}
pub struct DetailedPartialMatchForallConclusionArgsProof {
    pub substitution: HashMap<IdentifierId, Obj>,
    pub arg_match_proofs: Vec<ForallConclusionArgMatchProof>,
}
impl PartialMatchForallConclusionArgsProof {
    pub fn detail(&self) -> OutputDetail {
        match self {
            Self::Compact(_) => OutputDetail::Compact,
            Self::Normal(_) => OutputDetail::Normal,
            Self::Detailed(_) => OutputDetail::Detailed,
        }
    }
    pub(crate) fn new(
        detail: OutputDetail,
        substitution: HashMap<IdentifierId, Obj>,
        arg_match_proofs: Vec<ForallConclusionArgMatchProof>,
    ) -> RuntimeResult<Self> {
        for child in &arg_match_proofs {
            detail.require(child.detail(), "partial forall matching child")?;
        }
        Ok(match detail {
            OutputDetail::Compact => {
                Self::Compact(CompactPartialMatchForallConclusionArgsProof { substitution })
            }
            OutputDetail::Normal => {
                Self::Normal(NormalPartialMatchForallConclusionArgsProof { substitution })
            }
            OutputDetail::Detailed => {
                Self::Detailed(DetailedPartialMatchForallConclusionArgsProof {
                    substitution,
                    arg_match_proofs,
                })
            }
        })
    }
    pub(crate) fn into_parts(
        self,
        expected: OutputDetail,
    ) -> RuntimeResult<(
        HashMap<IdentifierId, Obj>,
        Vec<ForallConclusionArgMatchProof>,
    )> {
        expected.require(self.detail(), "partial forall matching")?;
        Ok(match self {
            Self::Compact(proof) => (proof.substitution, Vec::new()),
            Self::Normal(proof) => (proof.substitution, Vec::new()),
            Self::Detailed(proof) => (proof.substitution, proof.arg_match_proofs),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::runtime::RuntimeError;

    #[test]
    fn matching_stage_rejects_wrong_parent_and_child_modes() {
        let partial = PartialMatchForallConclusionArgsProof::new(
            OutputDetail::Normal,
            HashMap::new(),
            Vec::new(),
        )
        .unwrap();
        assert!(matches!(
            partial.into_parts(OutputDetail::Compact),
            Err(RuntimeError::InternalBug(_))
        ));
        let matched = MatchForallConclusionArgsProof::new(
            OutputDetail::Compact,
            HashMap::new(),
            Vec::new(),
            Vec::new(),
        )
        .unwrap();
        assert!(matches!(
            matched.into_parts(OutputDetail::Detailed),
            Err(RuntimeError::InternalBug(_))
        ));
        let wrong_child = ForallConclusionArgMatchProof::Normal(
            super::super::verify_equality::result::NormalForallConclusionArgMatchProof {},
        );
        assert!(matches!(
            PartialMatchForallConclusionArgsProof::new(
                OutputDetail::Compact,
                HashMap::new(),
                vec![wrong_child]
            ),
            Err(RuntimeError::InternalBug(_))
        ));
    }
}
