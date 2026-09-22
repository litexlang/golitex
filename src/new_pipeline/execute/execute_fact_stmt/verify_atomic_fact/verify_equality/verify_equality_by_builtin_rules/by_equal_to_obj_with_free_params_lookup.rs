use super::alpha_equal_helper::free_params_shapes_alpha_equal;
use crate::new_pipeline::ast::fact::EqualFact;
use crate::new_pipeline::ast::obj::Obj;
use crate::new_pipeline::exec_env::KnownEqualToObjWithFreeParamsShape;
use crate::new_pipeline::exec_env::known_fact_memory::free_params_shape_from_obj;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{FactId, Runtime, RuntimeResult};

// Builtin: prove `name = literal_fn_set` (or SetBuilder / AnonymousFn) when
// `known_equal_to_obj_with_free_params` indexes `name` to an alpha-equal shape.
//
// Mathematical property: membership and equality reasoning may cite a stored
// equality `a = rhs` where `rhs` carries binders; the index remembers that
// shape for `a` without object-definition unfold.
// Example: `trust g = fn(y R) R` then prove `g = fn(x R) R`.
//
// Does not replace ByFnSetAlphaEqual for two literal FnSets on the goal.
pub struct ByEqualToObjWithFreeParamsLookupBuiltinRuleProof {
    pub cite_index_fact_id: FactId,
}

impl Runtime {
    pub fn search_equal_fact_builtin_rule_by_equal_to_obj_with_free_params_lookup(
        &mut self,
        fact: &EqualFact,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<ByEqualToObjWithFreeParamsLookupBuiltinRuleProof>> {
        if let Some(proof) = self.try_equal_to_obj_with_free_params_lookup_one_way(
            &fact.left,
            &fact.right,
        )? {
            return Ok(Some(proof));
        }
        if let Some(proof) = self.try_equal_to_obj_with_free_params_lookup_one_way(
            &fact.right,
            &fact.left,
        )? {
            return Ok(Some(proof));
        }
        Ok(None)
    }

    fn try_equal_to_obj_with_free_params_lookup_one_way(
        &self,
        lookup_side: &Obj,
        shape_side: &Obj,
    ) -> RuntimeResult<Option<ByEqualToObjWithFreeParamsLookupBuiltinRuleProof>> {
        if free_params_shape_from_obj(lookup_side).is_some() {
            return Ok(None);
        }
        let Some(goal_shape) = free_params_shape_from_obj(shape_side) else {
            return Ok(None);
        };
        for (stored_shape, cite_index_fact_id) in
            self.collect_equal_to_obj_with_free_params_lookup_entries(lookup_side)
        {
            if free_params_shapes_alpha_equal(&stored_shape, &goal_shape) {
                return Ok(Some(
                    ByEqualToObjWithFreeParamsLookupBuiltinRuleProof {
                        cite_index_fact_id,
                    },
                ));
            }
        }
        Ok(None)
    }

    pub(crate) fn collect_equal_to_obj_with_free_params_lookup_entries(
        &self,
        obj: &Obj,
    ) -> Vec<(KnownEqualToObjWithFreeParamsShape, FactId)> {
        let mut keys = self.equivalence_class_keys(obj);
        let self_ir = obj.ir();
        if !keys.iter().any(|k| k == &self_ir) {
            keys.push(self_ir);
        }
        let mut out = Vec::new();
        for env in self.execution_environments_stack.iter().rev() {
            for key in &keys {
                let Some(entries) = env
                    .facts
                    .known_equal_to_obj_with_free_params
                    .by_other_side
                    .get(key)
                else {
                    continue;
                };
                out.extend(entries.iter().cloned());
            }
        }
        out
    }
}
