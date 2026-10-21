//! Uniqueness of real sequence limits, consuming previously established candidates.
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::AtomicExceptEqualityFactKnownProof;
use crate::prelude::*;

pub enum SequenceLimsupEqualityProof {
    SelectedValue(SequenceLimsupSelectedValueProof),
    Uniqueness(SequenceLimsupUniquenessProof),
}
pub struct SequenceLimsupSelectedValueProof {
    pub candidate: AtomicExceptEqualityFactKnownProof,
    pub value_equality: Box<EqualFactSearchedProof>,
}
pub struct SequenceLimsupUniquenessProof {
    pub left: AtomicExceptEqualityFactKnownProof,
    pub right: AtomicExceptEqualityFactKnownProof,
}
impl Runtime {
    // limsup(a)=L only after a stored has_seq_limsup(a,L); no inspection of a's body.
    pub(super) fn search_sequence_limsup_equality(
        &mut self,
        fact: &EqualFact,
    ) -> Option<SequenceLimsupEqualityProof> {
        for (selected, value) in [(&fact.left, &fact.right), (&fact.right, &fact.left)] {
            if let Obj::LimitOperator(LimitOperator::SequenceLimsup(limit)) = selected {
                for established in self.known_sequence_limsup_candidates() {
                    let query = self.sequence_limsup_candidate(
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
                        return Some(SequenceLimsupEqualityProof::SelectedValue(
                            SequenceLimsupSelectedValueProof {
                                candidate,
                                value_equality: Box::new(value_equality),
                            },
                        ));
                    }
                }
            }
        }
        for candidate in self.known_sequence_limsup_candidates() {
            let left =
                self.sequence_limsup_candidate(candidate.sequence.clone(), fact.left.clone());
            let right = self.sequence_limsup_candidate(candidate.sequence, fact.right.clone());
            if let (Some(left), Some(right)) = (
                self.lookup_known_atomic_premise(left.into()),
                self.lookup_known_atomic_premise(right.into()),
            ) {
                return Some(SequenceLimsupEqualityProof::Uniqueness(
                    SequenceLimsupUniquenessProof { left, right },
                ));
            }
        }
        None
    }
}
impl SequenceLimsupEqualityProof {
    pub fn rule_id(&self) -> &'static str {
        match self {
            Self::SelectedValue(_) => "SequenceLimsupSelectedValue",
            Self::Uniqueness(_) => "SequenceLimsupUniqueness",
        }
    }
    pub fn law(&self) -> &'static str {
        match self {
            Self::SelectedValue(_) => "has_seq_limsup(a,L) implies limsup(a)=L",
            Self::Uniqueness(_) => "Two finite real limits of the same sequence are equal",
        }
    }
}
