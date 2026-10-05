//! Cite-only membership transport along one already established subset.
use super::structural_membership_proof::KnownSubsetMembershipProof;
use super::verify_atomic_except_equality::result::AtomicExceptEqualityFactKnownProof;
use crate::ast::fact::{AtomicFact, InFact, SubsetFact};
use crate::ast::names::AtomicName;
use crate::parse::keywords::SUBSET;
use crate::runtime::Runtime;

impl Runtime {
    // No new truth/WD search: both premises must be visible stored facts.
    // This supplies x in R from x in S and S subset R inside bounded WD.
    pub(super) fn lookup_structural_known_subset_membership(
        &mut self,
        goal: &AtomicFact,
    ) -> Option<KnownSubsetMembershipProof> {
        let AtomicFact::InFact(member_goal) = goal else {
            return None;
        };
        let key = (
            AtomicName::Plain {
                name: SUBSET.into(),
            },
            true,
        );
        let subsets: Vec<SubsetFact> = self
            .execution_environments_stack
            .iter()
            .rev()
            .filter_map(|env| {
                env.facts
                    .known_atomic_except_equality_facts
                    .by_prop
                    .get(&key)
            })
            .flat_map(|knowns| knowns.iter())
            .filter_map(|known| match known {
                AtomicFact::SubsetFact(subset) => Some(subset.clone()),
                _ => None,
            })
            .collect();
        // Filter stored subset endpoints before looking up a member. This
        // avoids an all-members-by-all-members scan on every carrier query.
        for known in subsets {
            if self
                .lookup_known_obj_equality(&known.right, &member_goal.set)
                .is_none()
            {
                continue;
            }
            let source = known.left;
            let member = AtomicFact::InFact(InFact {
                fact_id: self.global_ids.allocate_fact_id(),
                element: member_goal.element.clone(),
                set: source.clone(),
                line_file: member_goal.line_file.clone(),
            });
            let Some(member_proof) = self.lookup_known_atomic_premise(member) else {
                continue;
            };
            let subset = AtomicFact::SubsetFact(SubsetFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left: source,
                right: member_goal.set.clone(),
                line_file: member_goal.line_file.clone(),
            });
            let Some(subset_proof): Option<AtomicExceptEqualityFactKnownProof> =
                self.lookup_known_atomic_premise(subset)
            else {
                continue;
            };
            return Some(KnownSubsetMembershipProof::new(member_proof, subset_proof));
        }
        None
    }
}
