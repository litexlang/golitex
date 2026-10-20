use super::result::AtomicExceptEqualityFactSearchedProof;
use crate::ast::fact::{AtomicFact, InFact};
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::{Runtime, RuntimeResult};

impl Runtime {
    /// Membership owns declaration conversion. The outer caller has checked
    /// WD and tried Direct on the original goal. Conversion does not consume
    /// or reopen a search stage: native membership gets exactly the same state.
    pub(super) fn search_in_fact_proof(
        &mut self,
        member: &InFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<AtomicExceptEqualityFactSearchedProof>> {
        let mut expansions = self.expand_template_membership(member)?;
        for index in 0..expansions.len() {
            let residual = AtomicFact::InFact(expansions[index].clone());
            let proof = self.search_atomic_except_equality_fact_proof_directly(&residual)?;
            let proof = match proof {
                Some(proof) => Some(proof),
                None if index + 1 == expansions.len() => {
                    self.search_atomic_except_equality_fact_proof_by_rules(&residual, state)?
                }
                None => None,
            };
            if let Some(residual) = proof {
                expansions.truncate(index + 1);
                return Ok(Some(
                    AtomicExceptEqualityFactSearchedProof::ByTemplateMembership(
                        TemplateMembershipProof {
                            expansions,
                            residual: Box::new(residual),
                        },
                    ),
                ));
            }
        }
        // Existing exact facts, equality transport and explicit rules remain
        // available on the surface instance if native conversion cannot prove it.
        self.search_atomic_except_equality_fact_proof_by_rules(
            &AtomicFact::InFact(member.clone()),
            state,
        )
    }
}

/// Successful carrier-conversion steps followed by the native truth evidence.
/// Formation comes from the enclosing verified source membership; no premise
/// is fabricated and no unsuccessful verification is embedded in this proof.
pub struct TemplateMembershipProof {
    pub expansions: Vec<InFact>,
    pub residual: Box<AtomicExceptEqualityFactSearchedProof>,
}

#[cfg(test)]
#[path = "../../../../../tests/unit/execute/template_type_interfaces/tests.rs"]
mod tests;
