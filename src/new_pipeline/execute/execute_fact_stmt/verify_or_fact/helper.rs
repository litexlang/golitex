use crate::new_pipeline::ast::fact::{AtomicFact, EqualFact, Fact, InFact};
use crate::new_pipeline::ast::obj::{Obj, StandardSet};
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

pub(super) fn objs_same(left: &Obj, right: &Obj) -> bool {
    left.ir() == right.ir()
}

// Equality may flip operands relative to the order pair.
pub(super) fn equal_matches_pair(eq: &EqualFact, left: &Obj, right: &Obj) -> bool {
    (objs_same(&eq.left, left) && objs_same(&eq.right, right))
        || (objs_same(&eq.left, right) && objs_same(&eq.right, left))
}

impl Runtime {
    // Prove `left $in R` and `right $in R`. Soft miss either side → None.
    pub(super) fn prove_both_objs_in_r(
        &mut self,
        left: &Obj,
        right: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<(VerifyFactResult, VerifyFactResult)>> {
        let left_fact_id = self.ids.allocate_fact_id();
        let left_in_r = self.verify_fact(
            &Fact::AtomicFact(AtomicFact::InFact(InFact {
                fact_id: left_fact_id,
                element: left.clone(),
                set: Obj::StandardSet(StandardSet::R),
                line_file: None,
            })),
            verify_state.clone(),
        )?;
        if left_in_r.is_failed() {
            return Ok(None);
        }
        let right_fact_id = self.ids.allocate_fact_id();
        let right_in_r = self.verify_fact(
            &Fact::AtomicFact(AtomicFact::InFact(InFact {
                fact_id: right_fact_id,
                element: right.clone(),
                set: Obj::StandardSet(StandardSet::R),
                line_file: None,
            })),
            verify_state,
        )?;
        if right_in_r.is_failed() {
            return Ok(None);
        }
        Ok(Some((left_in_r, right_in_r)))
    }
}
