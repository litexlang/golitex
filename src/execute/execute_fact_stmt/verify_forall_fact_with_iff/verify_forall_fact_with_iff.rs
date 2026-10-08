use crate::ast::fact::{ForallFact, ForallFactWithIff};
use crate::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::execute::execute_fact_stmt::verify_forall_fact_with_iff::result::{
    forall_fact_with_iff_result_from_iff_implies_then_fail,
    forall_fact_with_iff_result_from_success,
    forall_fact_with_iff_result_from_then_implies_iff_fail,
};
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // Split `forall ... <=>:` into two foralls and prove both directions.
    // 1. dom + then ⇒ iff
    // 2. dom + iff ⇒ then
    // Example:
    //   forall x, y R:
    //       =>:
    //           x = y
    //       <=>:
    //           y = x
    pub fn verify_forall_fact_with_iff(
        &mut self,
        fact: &ForallFactWithIff,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyFactResult> {
        let (then_implies_iff_goal, iff_implies_then_goal) =
            self.forall_with_iff_to_two_directions(fact);

        let then_implies_iff =
            self.verify_forall_fact(&then_implies_iff_goal, verify_state.clone())?;
        if then_implies_iff.is_failed() {
            return Ok(forall_fact_with_iff_result_from_then_implies_iff_fail(
                fact,
                then_implies_iff,
            ));
        }

        let iff_implies_then = self.verify_forall_fact(&iff_implies_then_goal, verify_state)?;
        if iff_implies_then.is_failed() {
            return Ok(forall_fact_with_iff_result_from_iff_implies_then_fail(
                fact,
                then_implies_iff,
                iff_implies_then,
            ));
        }

        Ok(forall_fact_with_iff_result_from_success(
            fact,
            then_implies_iff,
            iff_implies_then,
        ))
    }

    // Build the two direction foralls with fresh FactIds (not stored unless parent stores the iff).
    fn forall_with_iff_to_two_directions(
        &mut self,
        forall_iff: &ForallFactWithIff,
    ) -> (ForallFact, ForallFact) {
        let f = &forall_iff.forall_fact;
        let line_file = forall_iff.line_file.clone().or_else(|| f.line_file.clone());

        let mut dom_then = f.dom_facts.clone();
        for then in &f.then_facts {
            dom_then.push(then.clone().into());
        }
        let then_implies_iff = ForallFact {
            fact_id: self.global_ids.allocate_fact_id(),
            typed_parameters: f.typed_parameters.clone(),
            dom_facts: dom_then,
            then_facts: forall_iff.iff_facts.clone(),
            line_file: line_file.clone(),
        };

        let mut dom_iff = f.dom_facts.clone();
        for iff in &forall_iff.iff_facts {
            dom_iff.push(iff.clone().into());
        }
        let iff_implies_then = ForallFact {
            fact_id: self.global_ids.allocate_fact_id(),
            typed_parameters: f.typed_parameters.clone(),
            dom_facts: dom_iff,
            then_facts: f.then_facts.clone(),
            line_file,
        };

        (then_implies_iff, iff_implies_then)
    }
}
