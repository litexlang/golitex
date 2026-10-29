use super::well_defined_result::{
    PredicateDomainArgumentMembershipProof, PredicateDomainRequirementProof,
    PredicateDomainWellDefinedProof,
};
use crate::prelude::*;

impl Runtime {
    // Every supplied argument has already passed object WD in this caller.
    // Preserve ordinary verification priority, then derive the same membership
    // from a checked operand without rerunning its WD at a reduced ceiling.
    pub(in crate::execute) fn verify_requirement_with_checked_arguments(
        &mut self,
        requirement: &Fact,
        arguments: &[&Obj],
        requirement_index: usize,
        state: VerifyState,
    ) -> RuntimeResult<Result<PredicateDomainWellDefinedProof, VerifyFactResult>> {
        let result = self.verify_fact(requirement, state)?;
        if !result.is_failed() {
            return Ok(Ok(PredicateDomainWellDefinedProof {
                requirement: requirement.clone(),
                result: PredicateDomainRequirementProof::Verified(Box::new(result)),
            }));
        }
        if let Fact::AtomicFact(AtomicFact::InFact(member)) = requirement {
            if let Obj::StandardSet(target) = &member.set {
                let index = if arguments.get(requirement_index).copied() == Some(&member.element) {
                    Some(requirement_index)
                } else {
                    arguments
                        .iter()
                        .position(|argument| *argument == &member.element)
                };
                if let Some(index) = index {
                    if let Some(membership) =
                        self.search_membership_of_checked_object(&member.element, target, state)
                    {
                        return Ok(Ok(PredicateDomainWellDefinedProof {
                            requirement: requirement.clone(),
                            result: PredicateDomainRequirementProof::CheckedArgument(
                                PredicateDomainArgumentMembershipProof::new(
                                    requirement.clone(),
                                    index,
                                    membership,
                                ),
                            ),
                        }));
                    }
                }
            }
        }
        Ok(Err(result))
    }
}
