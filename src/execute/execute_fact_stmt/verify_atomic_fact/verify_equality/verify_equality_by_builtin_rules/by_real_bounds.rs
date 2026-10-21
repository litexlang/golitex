//! Selected real bounds are equal to previously proved extremal candidates.
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::AtomicExceptEqualityFactKnownProof;
use crate::prelude::*;
pub enum RealBoundEqualityProof {
    Supremum(SupremumSelectedValueProof),
    Infimum(InfimumSelectedValueProof),
}
pub struct SupremumSelectedValueProof {
    pub candidate: AtomicExceptEqualityFactKnownProof,
    pub value_equality: Box<EqualFactSearchedProof>,
}
pub struct InfimumSelectedValueProof {
    pub candidate: AtomicExceptEqualityFactKnownProof,
    pub value_equality: Box<EqualFactSearchedProof>,
}
impl Runtime {
    pub(super) fn search_real_bound_equality(
        &mut self,
        fact: &EqualFact,
    ) -> Option<RealBoundEqualityProof> {
        for (selected, value) in [(&fact.left, &fact.right), (&fact.right, &fact.left)] {
            let (set, direction) = match selected {
                Obj::BoundOperator(BoundOperator::Supremum(x)) => {
                    (x.set.as_ref(), RealBoundDirection::Upper)
                }
                Obj::BoundOperator(BoundOperator::Infimum(x)) => {
                    (x.set.as_ref(), RealBoundDirection::Lower)
                }
                _ => continue,
            };
            for established in self.known_real_bound_candidates(direction) {
                let query = self.real_bound_certificate(
                    set.clone(),
                    established.body[1].clone(),
                    direction,
                );
                let Some(candidate) = self.lookup_known_atomic_premise(query) else {
                    continue;
                };
                let comparison = EqualFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    left: established.body[1].clone(),
                    right: value.clone(),
                    line_file: None,
                };
                let Some(value_equality) = self.search_equal_fact_proof_directly(&comparison)
                else {
                    continue;
                };
                return Some(match direction {
                    RealBoundDirection::Upper => {
                        RealBoundEqualityProof::Supremum(SupremumSelectedValueProof {
                            candidate,
                            value_equality: Box::new(value_equality),
                        })
                    }
                    RealBoundDirection::Lower => {
                        RealBoundEqualityProof::Infimum(InfimumSelectedValueProof {
                            candidate,
                            value_equality: Box::new(value_equality),
                        })
                    }
                });
            }
        }
        None
    }
}
impl RealBoundEqualityProof {
    pub fn rule_id(&self) -> &'static str {
        match self {
            Self::Supremum(_) => "SupremumSelectedValue",
            Self::Infimum(_) => "InfimumSelectedValue",
        }
    }
    pub fn law(&self) -> &'static str {
        "A proved finite extremal candidate determines the selected bound"
    }
    pub fn candidate(&self) -> &AtomicExceptEqualityFactKnownProof {
        match self {
            Self::Supremum(p) => &p.candidate,
            Self::Infimum(p) => &p.candidate,
        }
    }
    pub fn value_equality(&self) -> &EqualFactSearchedProof {
        match self {
            Self::Supremum(p) => &p.value_equality,
            Self::Infimum(p) => &p.value_equality,
        }
    }
}
