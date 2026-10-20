//! Uniqueness of real function limits, consuming previously established candidates.
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::AtomicExceptEqualityFactKnownProof;
use crate::prelude::*;

pub enum FunctionLimitEqualityProof {
    SelectedValue(FunctionLimitSelectedValueProof),
    Uniqueness(FunctionLimitUniquenessProof),
}
pub struct FunctionLimitSelectedValueProof {
    pub candidate: AtomicExceptEqualityFactKnownProof,
    pub value_equality: Box<EqualFactSearchedProof>,
}
pub struct FunctionLimitUniquenessProof {
    pub left: AtomicExceptEqualityFactKnownProof,
    pub right: AtomicExceptEqualityFactKnownProof,
}
impl Runtime {
    // lim(f,x0)=L consumes a stored candidate at this exact point.
    pub(super) fn search_function_limit_equality(
        &mut self,
        fact: &EqualFact,
    ) -> Option<FunctionLimitEqualityProof> {
        for (selected, value) in [(&fact.left, &fact.right), (&fact.right, &fact.left)] {
            if let Obj::LimitOperator(LimitOperator::Function(limit)) = selected {
                for established in self.known_function_limit_candidates() {
                    let query = self.function_limit_candidate(
                        *limit.function.clone(),
                        limit.approach.clone(),
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
                    // Read-only equality/closed exact arithmetic only, never a new limit search.
                    if let Some(value_equality) = self.search_equal_fact_proof_directly(&comparison)
                    {
                        return Some(FunctionLimitEqualityProof::SelectedValue(
                            FunctionLimitSelectedValueProof {
                                candidate,
                                value_equality: Box::new(value_equality),
                            },
                        ));
                    }
                }
            }
        }
        for candidate in self.known_function_limit_candidates() {
            let left = self.function_limit_candidate(
                candidate.function.clone(),
                candidate.approach.clone(),
                fact.left.clone(),
            );
            let right = self.function_limit_candidate(
                candidate.function,
                candidate.approach.clone(),
                fact.right.clone(),
            );
            if let (Some(left), Some(right)) = (
                self.lookup_known_atomic_premise(left.into()),
                self.lookup_known_atomic_premise(right.into()),
            ) {
                return Some(FunctionLimitEqualityProof::Uniqueness(
                    FunctionLimitUniquenessProof { left, right },
                ));
            }
        }
        None
    }
}
impl FunctionLimitEqualityProof {
    pub fn rule_id(&self) -> &'static str {
        match self {
            Self::SelectedValue(_) => "FunctionLimitSelectedValue",
            Self::Uniqueness(_) => "FunctionLimitUniqueness",
        }
    }
    pub fn law(&self) -> &'static str {
        match self {
            Self::SelectedValue(_) => {
                "A proved candidate determines the selected value for the same approach"
            }
            Self::Uniqueness(_) => {
                "Two finite real limits of the same function, point and direction are equal"
            }
        }
    }
}
