use super::result::AtomicExceptEqualityFactKnownProof;
use super::search_atomic_except_equality_fact_proof_by_known_special_property::InFactSearchProofByKnownSpecialProperty;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::KnownEqualityPathProof;
use crate::prelude::*;

impl Runtime {
    // All sets in P(X) stay in P(X) under union; intersection needs either
    // operand and difference needs its left operand. For example, typed
    // E,F in P(X) make p(union(E,F)) a valid call during a struct-law check.
    // Read existing membership/equality evidence only; never reopen premise search.
    pub(super) fn known_power_set_closure(
        &mut self,
        fact: &InFact,
    ) -> Option<InFactSearchProofByKnownSpecialProperty> {
        use InFactSearchProofByKnownSpecialProperty as P;
        let Obj::SetOperator(SetOperator::PowerSet(power)) = &fact.set else {
            return None;
        };
        match &fact.element {
            Obj::SetFormer(SetFormer::ListSet(value)) => {
                let mut members = Vec::new();
                for element in &value.list {
                    let query = AtomicFact::InFact(InFact {
                        fact_id: self.global_ids.allocate_fact_id(),
                        element: element.as_ref().clone(),
                        set: power.set.as_ref().clone(),
                        line_file: None,
                    });
                    members.push(self.lookup_known_atomic_premise(query)?);
                }
                Some(P::ListSetInPowerSetFromMembers(
                    ListSetInPowerSetFromMembersProof { members },
                ))
            }
            Obj::SetOperator(SetOperator::Union(value)) => {
                let left = self.known_power_set_operand(&value.left, &fact.set)?;
                let right = self.known_power_set_operand(&value.right, &fact.set)?;
                Some(P::UnionInPowerSet(UnionInPowerSetProof::new(left, right)))
            }
            Obj::SetOperator(SetOperator::Intersect(value)) => {
                if let Some(left) = self.known_power_set_operand(&value.left, &fact.set) {
                    return Some(P::IntersectInPowerSetFromLeft(
                        IntersectInPowerSetFromLeftProof::new(left),
                    ));
                }
                let right = self.known_power_set_operand(&value.right, &fact.set)?;
                Some(P::IntersectInPowerSetFromRight(
                    IntersectInPowerSetFromRightProof::new(right),
                ))
            }
            Obj::SetOperator(SetOperator::SetMinus(value)) => {
                if let Some(left) = self.known_power_set_operand(&value.left, &fact.set) {
                    return Some(P::SetMinusInPowerSet(SetMinusInPowerSetProof::new(left)));
                }
                // X minus B is always a subset of X. Identity or an actual
                // stored carrier equality suffices; no self-membership search.
                let path = self.exact_property_equality_path(&value.left, &power.set)?;
                Some(P::SetMinusInPowerSetOfLeft(SetMinusInPowerSetOfLeftProof {
                    left_equal_carrier: KnownEqualityPathProof::new(path),
                }))
            }
            _ => None,
        }
    }

    fn known_power_set_operand(
        &mut self,
        element: &Obj,
        power_set: &Obj,
    ) -> Option<AtomicExceptEqualityFactKnownProof> {
        let query = AtomicFact::InFact(InFact {
            fact_id: self.global_ids.allocate_fact_id(),
            element: element.clone(),
            set: power_set.clone(),
            line_file: None,
        });
        self.lookup_known_atomic_premise(query)
    }
}

// Literal WD already checked every child and its required distinctness.
// Only the original known point memberships license the carrier bound.
pub struct ListSetInPowerSetFromMembersProof {
    pub members: Vec<AtomicExceptEqualityFactKnownProof>,
}

pub struct UnionInPowerSetProof {
    pub left: AtomicExceptEqualityFactKnownProof,
    pub right: AtomicExceptEqualityFactKnownProof,
}
impl UnionInPowerSetProof {
    pub fn new(
        left: AtomicExceptEqualityFactKnownProof,
        right: AtomicExceptEqualityFactKnownProof,
    ) -> Self {
        Self { left, right }
    }
}

pub struct IntersectInPowerSetFromLeftProof {
    pub left: AtomicExceptEqualityFactKnownProof,
}
impl IntersectInPowerSetFromLeftProof {
    pub fn new(left: AtomicExceptEqualityFactKnownProof) -> Self {
        Self { left }
    }
}

pub struct IntersectInPowerSetFromRightProof {
    pub right: AtomicExceptEqualityFactKnownProof,
}
impl IntersectInPowerSetFromRightProof {
    pub fn new(right: AtomicExceptEqualityFactKnownProof) -> Self {
        Self { right }
    }
}

pub struct SetMinusInPowerSetProof {
    pub left: AtomicExceptEqualityFactKnownProof,
}

pub struct SetMinusInPowerSetOfLeftProof {
    pub left_equal_carrier: KnownEqualityPathProof,
}
impl SetMinusInPowerSetProof {
    pub fn new(left: AtomicExceptEqualityFactKnownProof) -> Self {
        Self { left }
    }
}
