use crate::ast::fact::{AtomicFact, Fact, InFact};
use crate::ast::obj::{Obj, SetFormer, SetOperator};
use crate::runtime::{Runtime, RuntimeResult};
use crate::store_fact_and_infer::{
    InferAtomicExceptEqualityResult, InferPowerSetMembershipProjectionResult,
    InferSetBuilderMembershipProjectionResult,
};

impl Runtime {
    // Collect every InFact membership infer rule that fires (may be several families).
    pub(super) fn infer_in_fact_rules(
        &mut self,
        in_fact: &InFact,
        verify_state: crate::execute::execute_fact_stmt::VerifyState,
    ) -> RuntimeResult<Vec<InferAtomicExceptEqualityResult>> {
        let mut rules = Vec::new();
        if let Some(builder) = self.resolve_set_builder_for_membership_projection(&in_fact.set) {
            let mut derived = Vec::new();
            let fact_id = self.global_ids.allocate_fact_id();
            let base_in = AtomicFact::InFact(InFact {
                fact_id,
                element: in_fact.element.clone(),
                set: builder.param_set.as_ref().clone(),
                line_file: in_fact.line_file.clone(),
            });
            self.store_new_set_builder_projection(
                &Fact::AtomicFact(base_in),
                verify_state,
                &mut derived,
            )?;
            let mut subst = std::collections::HashMap::new();
            subst.insert(builder.param_binding.id, in_fact.element.clone());
            for defining in &builder.facts {
                let Ok(qf) = self.inst_quantifier_free_fact(defining, &subst) else {
                    continue;
                };
                let projected = crate::instantiate::quantifier_free_fact_to_fact(qf);
                self.store_new_set_builder_projection(&projected, verify_state, &mut derived)?;
            }
            rules.push(InferAtomicExceptEqualityResult::InFactSetBuilder(
                InferSetBuilderMembershipProjectionResult { derived },
            ));
        }
        if let Some(base) = self.resolve_power_set_base_for_membership_projection(&in_fact.set) {
            let fact_id = self.global_ids.allocate_fact_id();
            let subset = AtomicFact::SubsetFact(crate::ast::fact::SubsetFact {
                fact_id,
                left: in_fact.element.clone(),
                right: base,
                line_file: in_fact.line_file.clone(),
            });
            let derived = Box::new(
                self.store_inferred_fact_and_infer(&Fact::AtomicFact(subset), verify_state)?,
            );
            rules.push(InferAtomicExceptEqualityResult::InFactPowerSet(
                InferPowerSetMembershipProjectionResult { derived },
            ));
        }
        rules.extend(self.infer_in_fact_list_set_ops_rules(in_fact, verify_state)?);
        rules.extend(self.infer_in_fact_cart_interval_rules(in_fact, verify_state)?);
        rules.extend(self.infer_in_fact_signed_standard_set_rules(in_fact, verify_state)?);
        rules.extend(self.infer_in_fact_fn_rules(in_fact, verify_state)?);
        rules.extend(self.infer_in_fact_index_family_rules(in_fact, verify_state)?);
        Ok(rules)
    }
}

impl Runtime {
    // The source membership is stored before inference. A builder reached
    // through equality can project that same membership (or cycle through a
    // second carrier). Re-inferencing a visible fact adds no consequence.
    // This guard belongs to this projection rule, not to truth search/store.
    fn store_new_set_builder_projection(
        &mut self,
        projected: &Fact,
        verify_state: crate::execute::execute_fact_stmt::VerifyState,
        derived: &mut Vec<crate::store_fact_and_infer::StoreFactAndInferResult>,
    ) -> RuntimeResult<()> {
        let key = projected.ir();
        let already_stored = self.execution_environments_stack.iter().rev().any(|env| {
            env.facts.facts_by_id.values().any(|known| {
                std::mem::discriminant(known) == std::mem::discriminant(projected)
                    && known.ir() == key
            })
        });
        if !already_stored {
            derived.push(self.store_inferred_fact_and_infer(projected, verify_state)?);
        }
        Ok(())
    }

    fn resolve_set_builder_for_membership_projection(
        &self,
        set: &Obj,
    ) -> Option<crate::ast::obj::SetBuilder> {
        if let Obj::SetFormer(SetFormer::SetBuilder(builder)) = set {
            return Some(builder.clone());
        }
        let adjacency = self.visible_equivalence_class_adjacency();
        let neighbors = adjacency.get(&set.ir())?;
        for (_peer_key, equal_fact) in neighbors.iter() {
            let peer = if equal_fact.left.ir() == set.ir() {
                &equal_fact.right
            } else {
                &equal_fact.left
            };
            if let Obj::SetFormer(SetFormer::SetBuilder(builder)) = peer {
                return Some(builder.clone());
            }
        }
        None
    }

    fn resolve_power_set_base_for_membership_projection(&self, set: &Obj) -> Option<Obj> {
        if let Obj::SetOperator(SetOperator::PowerSet(power)) = set {
            return Some(power.set.as_ref().clone());
        }
        let adjacency = self.visible_equivalence_class_adjacency();
        let neighbors = adjacency.get(&set.ir())?;
        for (_peer_key, equal_fact) in neighbors.iter() {
            let peer = if equal_fact.left.ir() == set.ir() {
                &equal_fact.right
            } else {
                &equal_fact.left
            };
            if let Obj::SetOperator(SetOperator::PowerSet(power)) = peer {
                return Some(power.set.as_ref().clone());
            }
        }
        None
    }
}

#[cfg(test)]
#[path = "../../../../../tests/unit/execute/set_builder_projection_cycle/tests.rs"]
mod set_builder_projection_cycle_tests;
