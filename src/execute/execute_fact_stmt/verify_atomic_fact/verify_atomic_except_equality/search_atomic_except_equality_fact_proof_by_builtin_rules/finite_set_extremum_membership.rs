use crate::ast::fact::{EqualFact, InFact};
use crate::ast::obj::{Obj, FiniteSetStat};
use crate::runtime::Runtime;
use super::in_fact::{InFactSearchProofByBuiltinRule, FiniteSetMaxMemberBuiltinRuleProof, FiniteSetMinMemberBuiltinRuleProof};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_they_are_the_same::search_equal_fact_proof_by_they_are_the_same;

impl Runtime {
    // A finite nonempty real set contains its maximum. The enclosing InFact
    // has already checked all of these obligations via the maximum's WD.
    // Example: finite_set_max(S) $in S. Only identity/alpha matches the set.
    pub(super) fn finite_set_max_membership_proof(&mut self, fact: &InFact) -> Option<InFactSearchProofByBuiltinRule> {
        let Obj::FiniteSetStat(FiniteSetStat::FiniteSetMax(value)) = &fact.element else { return None; };
        let equal = EqualFact { fact_id: self.global_ids.allocate_fact_id(), left: value.set.as_ref().clone(), right: fact.set.clone(), line_file: fact.line_file.clone() };
        let set_equal = search_equal_fact_proof_by_they_are_the_same(&equal)?.into();
        Some(InFactSearchProofByBuiltinRule::FiniteSetMaxMember(FiniteSetMaxMemberBuiltinRuleProof { set_equal }))
    }

    // The corresponding minimum is also a member, under the same existing WD.
    // Example: finite_set_min(S) $in S; no inference about an unrelated set.
    pub(super) fn finite_set_min_membership_proof(&mut self, fact: &InFact) -> Option<InFactSearchProofByBuiltinRule> {
        let Obj::FiniteSetStat(FiniteSetStat::FiniteSetMin(value)) = &fact.element else { return None; };
        let equal = EqualFact { fact_id: self.global_ids.allocate_fact_id(), left: value.set.as_ref().clone(), right: fact.set.clone(), line_file: fact.line_file.clone() };
        let set_equal = search_equal_fact_proof_by_they_are_the_same(&equal)?.into();
        Some(InFactSearchProofByBuiltinRule::FiniteSetMinMember(FiniteSetMinMemberBuiltinRuleProof { set_equal }))
    }
}
