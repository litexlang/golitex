use super::well_defined_result::{
    PredicateDomainArgumentMembershipProof, PredicateDomainRequirementProof,
    PredicateDomainWellDefinedProof,
};
use crate::prelude::*;

impl Runtime {
    // Some specialized consumers still require the ordinary verified route.
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
        Ok(self
            .requirement_from_checked_arguments(requirement, arguments, requirement_index, state)
            .ok_or(result))
    }

    // Every supplied argument has already passed object WD in this caller.
    // Ordinary predicate domains support this existing evidence route directly.
    pub(in crate::execute) fn verify_requirement_with_checked_arguments_first(
        &mut self,
        requirement: &Fact,
        arguments: &[&Obj],
        requirement_index: usize,
        state: VerifyState,
    ) -> RuntimeResult<Result<PredicateDomainWellDefinedProof, VerifyFactResult>> {
        if let Some(proof) = self.requirement_from_checked_arguments(
            requirement,
            arguments,
            requirement_index,
            state,
        ) {
            return Ok(Ok(proof));
        }
        let result = self.verify_fact(requirement, state)?;
        if result.is_failed() {
            return Ok(Err(result));
        }
        Ok(Ok(PredicateDomainWellDefinedProof {
            requirement: requirement.clone(),
            result: PredicateDomainRequirementProof::Verified(Box::new(result)),
        }))
    }

    fn requirement_from_checked_arguments(
        &mut self,
        requirement: &Fact,
        arguments: &[&Obj],
        requirement_index: usize,
        state: VerifyState,
    ) -> Option<PredicateDomainWellDefinedProof> {
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
                        return Some(PredicateDomainWellDefinedProof {
                            requirement: requirement.clone(),
                            result: PredicateDomainRequirementProof::CheckedArgument(
                                PredicateDomainArgumentMembershipProof::new(
                                    requirement.clone(),
                                    index,
                                    membership,
                                ),
                            ),
                        });
                    }
                }
            }
        }
        None
    }
}
