//! Uniqueness of real sequence limits, consuming previously established candidates.
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::AtomicExceptEqualityFactKnownProof;
use crate::prelude::*;

pub enum SequenceLimitEqualityProof {
    SelectedValue(SequenceLimitSelectedValueProof),
    Uniqueness(SequenceLimitUniquenessProof),
}
pub struct SequenceLimitSelectedValueProof {
    pub candidate: AtomicExceptEqualityFactKnownProof,
}
pub struct SequenceLimitUniquenessProof {
    pub left: AtomicExceptEqualityFactKnownProof,
    pub right: AtomicExceptEqualityFactKnownProof,
}
impl Runtime {
    // lim(a)=L only after a stored has_seq_limit(a,L); no inspection of a's body.
    pub(super) fn search_sequence_limit_equality(
        &mut self,
        fact: &EqualFact,
    ) -> Option<SequenceLimitEqualityProof> {
        for (selected, value) in [(&fact.left, &fact.right), (&fact.right, &fact.left)] {
            if let Obj::LimitOperator(LimitOperator::Sequence(limit)) = selected {
                let candidate =
                    self.sequence_limit_candidate(*limit.sequence.clone(), value.clone());
                if let Some(candidate) = self.lookup_known_atomic_premise(candidate.into()) {
                    return Some(SequenceLimitEqualityProof::SelectedValue(
                        SequenceLimitSelectedValueProof { candidate },
                    ));
                }
            }
        }
        for candidate in self.known_sequence_limit_candidates() {
            let left = self.sequence_limit_candidate(candidate.sequence.clone(), fact.left.clone());
            let right = self.sequence_limit_candidate(candidate.sequence, fact.right.clone());
            if let (Some(left), Some(right)) = (
                self.lookup_known_atomic_premise(left.into()),
                self.lookup_known_atomic_premise(right.into()),
            ) {
                return Some(SequenceLimitEqualityProof::Uniqueness(
                    SequenceLimitUniquenessProof { left, right },
                ));
            }
        }
        None
    }
}
impl SequenceLimitEqualityProof {
    pub fn rule_id(&self) -> &'static str {
        match self {
            Self::SelectedValue(_) => "SequenceLimitSelectedValue",
            Self::Uniqueness(_) => "SequenceLimitUniqueness",
        }
    }
    pub fn law(&self) -> &'static str {
        match self {
            Self::SelectedValue(_) => "has_seq_limit(a,L) implies lim(a)=L",
            Self::Uniqueness(_) => "Two finite real limits of the same sequence are equal",
        }
    }
}
