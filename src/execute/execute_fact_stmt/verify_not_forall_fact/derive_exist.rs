use crate::ast::fact::{ExistShapedFact, NotForallFact, PlainExistFact};
use crate::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // not forall (dom => A and B) means exist (dom and (not A or not B)).
    pub(crate) fn not_forall_to_counterexample_exist(
        &mut self,
        not_forall: &NotForallFact,
    ) -> RuntimeResult<Option<ExistShapedFact>> {
        let Some(negated_body) = self.negate_quantifier_free_conjunction_to_conjuncts(
            &not_forall.then_facts,
            not_forall.line_file.clone(),
        )?
        else {
            return Ok(None);
        };
        let mut facts = not_forall.dom_facts.clone();
        facts.extend(negated_body);
        Ok(Some(ExistShapedFact::Exist(PlainExistFact {
            fact_id: self.global_ids.allocate_fact_id(),
            typed_parameters: not_forall.typed_parameters.clone(),
            facts,
            line_file: not_forall.line_file.clone(),
        })))
    }
}
