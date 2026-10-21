//! Uniqueness of real sequence limits, consuming previously established candidates.
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::AtomicExceptEqualityFactKnownProof;
use crate::prelude::*;

pub enum SequenceLiminfEqualityProof {
    SelectedValue(SequenceLiminfSelectedValueProof),
    Uniqueness(SequenceLiminfUniquenessProof),
}
pub struct SequenceLiminfSelectedValueProof {
    pub candidate: AtomicExceptEqualityFactKnownProof,
    pub value_equality: Box<EqualFactSearchedProof>,
}
pub struct SequenceLiminfUniquenessProof {
    pub left: AtomicExceptEqualityFactKnownProof,
    pub right: AtomicExceptEqualityFactKnownProof,
}
impl Runtime {
    // liminf(a)=L only after a stored has_seq_liminf(a,L); no inspection of a's body.
    pub(super) fn search_sequence_liminf_equality(
        &mut self,
        fact: &EqualFact,
    ) -> Option<SequenceLiminfEqualityProof> {
        for (selected, value) in [(&fact.left, &fact.right), (&fact.right, &fact.left)] {
            if let Obj::LimitOperator(LimitOperator::SequenceLiminf(limit)) = selected {
                for established in self.known_sequence_liminf_candidates() {
                    let query = self.sequence_liminf_candidate(
                        *limit.sequence.clone(),
                        established.value.clone(),
                    );
                    let Some(candidate) = self.lookup_known_atomic_premise(query.into()) else {
                        continue;
                    };
                    let comparison = EqualFact {
                        fact_id: self.global_ids.allocate_fact_id(),
                        left: established.value,
                        right: value.clone(),
                        line_file: None,
                    };
                    if let Some(value_equality) = self.search_equal_fact_proof_directly(&comparison)
                    {
                        return Some(SequenceLiminfEqualityProof::SelectedValue(
                            SequenceLiminfSelectedValueProof {
                                candidate,
                                value_equality: Box::new(value_equality),
                            },
                        ));
                    }
                }
            }
        }
        for candidate in self.known_sequence_liminf_candidates() {
            let left =
                self.sequence_liminf_candidate(candidate.sequence.clone(), fact.left.clone());
            let right = self.sequence_liminf_candidate(candidate.sequence, fact.right.clone());
            if let (Some(left), Some(right)) = (
                self.lookup_known_atomic_premise(left.into()),
                self.lookup_known_atomic_premise(right.into()),
            ) {
                return Some(SequenceLiminfEqualityProof::Uniqueness(
                    SequenceLiminfUniquenessProof { left, right },
                ));
            }
        }
        None
    }
}
impl SequenceLiminfEqualityProof {
    pub fn rule_id(&self) -> &'static str {
        match self {
            Self::SelectedValue(_) => "SequenceLiminfSelectedValue",
            Self::Uniqueness(_) => "SequenceLiminfUniqueness",
        }
    }
    pub fn law(&self) -> &'static str {
        match self {
            Self::SelectedValue(_) => "has_seq_liminf(a,L) implies liminf(a)=L",
            Self::Uniqueness(_) => "Two finite real limits of the same sequence are equal",
        }
    }
}
