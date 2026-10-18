//! Membership XOR: remove one sym_diff constructor, retaining both child proofs.
use super::result::*;
use crate::prelude::*;
impl Runtime {
    pub(super) fn search_sym_diff_membership_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: VerifyState,
    ) -> RuntimeResult<Option<AtomicExceptEqualityFactSearchProofByBuiltinStrategy>> {
        use AtomicExceptEqualityFactSearchProofByBuiltinStrategy as P;
        let (element, set, positive, line_file) = match fact {
            AtomicFact::InFact(f) => (&f.element, &f.set, true, &f.line_file),
            AtomicFact::NotInFact(f) => (&f.element, &f.set, false, &f.line_file),
            _ => return Ok(None),
        };
        let Obj::SetOperator(SetOperator::SymmetricDifference(s)) = set else {
            return Ok(None);
        };
        if positive {
            let requirements: Vec<Fact> = vec![
                InFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    element: element.clone(),
                    set: s.left.as_ref().clone(),
                    line_file: line_file.clone(),
                }
                .into(),
                NotInFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    element: element.clone(),
                    set: s.right.as_ref().clone(),
                    line_file: line_file.clone(),
                }
                .into(),
            ];
            if let Some((requirement_facts, proof_of_requirement_facts)) =
                self.verify_strategy_requirements(requirements, ctx)?
            {
                return Ok(Some(P::SymDiffMembershipLeft(
                    SymDiffMembershipLeftStrategySingleStep {
                        requirement_facts,
                        proof_of_requirement_facts,
                    },
                )));
            }
        }
        if positive {
            let requirements: Vec<Fact> = vec![
                NotInFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    element: element.clone(),
                    set: s.left.as_ref().clone(),
                    line_file: line_file.clone(),
                }
                .into(),
                InFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    element: element.clone(),
                    set: s.right.as_ref().clone(),
                    line_file: line_file.clone(),
                }
                .into(),
            ];
            if let Some((requirement_facts, proof_of_requirement_facts)) =
                self.verify_strategy_requirements(requirements, ctx)?
            {
                return Ok(Some(P::SymDiffMembershipRight(
                    SymDiffMembershipRightStrategySingleStep {
                        requirement_facts,
                        proof_of_requirement_facts,
                    },
                )));
            }
        }
        if !positive {
            let requirements: Vec<Fact> = vec![
                InFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    element: element.clone(),
                    set: s.left.as_ref().clone(),
                    line_file: line_file.clone(),
                }
                .into(),
                InFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    element: element.clone(),
                    set: s.right.as_ref().clone(),
                    line_file: line_file.clone(),
                }
                .into(),
            ];
            if let Some((requirement_facts, proof_of_requirement_facts)) =
                self.verify_strategy_requirements(requirements, ctx)?
            {
                return Ok(Some(P::SymDiffNonmembershipBoth(
                    SymDiffNonmembershipBothStrategySingleStep {
                        requirement_facts,
                        proof_of_requirement_facts,
                    },
                )));
            }
        }
        if !positive {
            let requirements: Vec<Fact> = vec![
                NotInFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    element: element.clone(),
                    set: s.left.as_ref().clone(),
                    line_file: line_file.clone(),
                }
                .into(),
                NotInFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    element: element.clone(),
                    set: s.right.as_ref().clone(),
                    line_file: line_file.clone(),
                }
                .into(),
            ];
            if let Some((requirement_facts, proof_of_requirement_facts)) =
                self.verify_strategy_requirements(requirements, ctx)?
            {
                return Ok(Some(P::SymDiffNonmembershipNeither(
                    SymDiffNonmembershipNeitherStrategySingleStep {
                        requirement_facts,
                        proof_of_requirement_facts,
                    },
                )));
            }
        }
        Ok(None)
    }
}
