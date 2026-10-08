//! Exact function-space membership: complete domain, then all return values.
use super::result::FunctionSetMembershipStrategySingleStep;
use crate::ast::fact::AtomicFact;
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::{Runtime, RuntimeResult};

impl Runtime {
    pub(super) fn search_function_set_membership_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: VerifyState,
    ) -> RuntimeResult<Option<FunctionSetMembershipStrategySingleStep>> {
        let AtomicFact::InFact(fact) = fact else {
            return Ok(None);
        };
        let Some(target) = self.function_space_signature(&fact.set) else {
            return Ok(None);
        };
        let Ok(domain) = self.verify_complete_function_domain(&fact.element, &target, ctx)? else {
            return Ok(None);
        };
        let Ok(requirements) = self.build_function_return_requirements(&fact.element, &target)
        else {
            return Ok(None);
        };
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, ctx)?
        else {
            return Ok(None);
        };
        Ok(Some(FunctionSetMembershipStrategySingleStep {
            domain,
            requirement_facts,
            proof_of_requirement_facts,
        }))
    }
}
