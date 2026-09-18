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
    pub fn search_equal_fact_by_closed_numeric_equal_substitution(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<ClosedNumericEqualSubstitutionBuiltinRewriteProof>> {
        let entries = self.visible_closed_numeric_equal_entries();
        for (from_ir, closed, fact_id) in &entries {
            let rewritten_left = replace_obj_matching_ir(&fact.left, from_ir, closed);
            let rewritten_right = replace_obj_matching_ir(&fact.right, from_ir, closed);
            if rewritten_left.ir() == fact.left.ir() && rewritten_right.ir() == fact.right.ir() {
                continue;
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
                continue;
            }
            return Ok(Some(ClosedNumericEqualSubstitutionBuiltinRewriteProof {
                rewritten_left,
                rewritten_right,
                cited_equal_fact_ids: vec![*fact_id],
                residual_equal,
            }));
        }
        Ok(None)
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
