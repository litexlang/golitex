use super::by_builtin_rewrite_result::ClosedNumericEqualSubstitutionBuiltinRewriteProof;
use super::search_equal_fact_by_congruence_substitution::replace_obj_matching_ir;
use crate::new_pipeline::ast::fact::EqualFact;
use crate::new_pipeline::ast::obj::Obj;
use crate::new_pipeline::exec_env::exec_env::SpecialObjProperty;
use crate::new_pipeline::exec_env::known_fact_memory::ObjIR;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::runtime_ids::FactId;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};
use std::collections::HashSet;

impl Runtime {
    // Builtin rewrite: substitute ClosedNumericEqual representatives into the goal.
    // Mathematical property / examples: see ClosedNumericEqualSubstitutionBuiltinRewriteProof.
    //
    // All visible ClosedNumericEqual hits that appear as subterms are applied in
    // one shot (cite every used FactId), so `a + b = 30` works after
    // `have a R = 10` and `have b R = 20`.
    pub fn search_equal_fact_by_closed_numeric_equal_substitution(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<ClosedNumericEqualSubstitutionBuiltinRewriteProof>> {
        let entries = self.visible_closed_numeric_equal_entries();
        let mut rewritten_left = fact.left.clone();
        let mut rewritten_right = fact.right.clone();
        let mut cited_equal_fact_ids = Vec::new();

        for (from_ir, closed, fact_id) in &entries {
            let next_left = replace_obj_matching_ir(&rewritten_left, from_ir, closed);
            let next_right = replace_obj_matching_ir(&rewritten_right, from_ir, closed);
            if next_left.ir() == rewritten_left.ir() && next_right.ir() == rewritten_right.ir() {
                continue;
            }
            rewritten_left = next_left;
            rewritten_right = next_right;
            cited_equal_fact_ids.push(*fact_id);
        }

        if cited_equal_fact_ids.is_empty() {
            return Ok(None);
        }

        let residual_fact_id = self.ids.allocate_fact_id();
        let residual = EqualFact {
            fact_id: residual_fact_id,
            left: rewritten_left.clone(),
            right: rewritten_right.clone(),
            line_file: fact.line_file.clone(),
        };
        let residual_state = VerifyState {
            can_use_forall_fact: verify_state.can_use_forall_fact,
            can_use_rewrite: false,
            store_well_defined_fact: false,
        };
        let residual_equal = self.verify_equal_fact(&residual, residual_state)?;
        if residual_equal.is_failed() {
            return Ok(None);
        }
        Ok(Some(ClosedNumericEqualSubstitutionBuiltinRewriteProof {
            rewritten_left,
            rewritten_right,
            cited_equal_fact_ids,
            residual_equal,
        }))
    }

    fn visible_closed_numeric_equal_entries(&self) -> Vec<(ObjIR, Obj, FactId)> {
        let mut seen: HashSet<u64> = HashSet::new();
        let mut out = Vec::new();
        for env in self.execution_environments_stack.iter().rev() {
            for (key, props) in env.special_object_properties.iter() {
                for prop in props {
                    if let SpecialObjProperty::ClosedNumericEqual((closed, fact_id)) = prop {
                        let id = fact_id.value();
                        if seen.insert(id) {
                            out.push((key.clone(), closed.clone(), *fact_id));
                        }
                    }
                }
            }
        }
        out
    }
}
