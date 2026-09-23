use crate::new_pipeline::ast::fact::{AtomicFact, Fact, InFact};
use crate::new_pipeline::ast::obj::{Obj, SetFormer, SetOperator};
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};
use crate::new_pipeline::store_fact_and_infer::{
    InferAtomicExceptEqualityResult, InferPowerSetMembershipProjectionResult,
    InferSetBuilderMembershipProjectionResult,
};

impl Runtime {
    // Collect every InFact membership infer rule that fires (may be several families).
    pub(super) fn infer_in_fact_rules(
        &mut self,
        in_fact: &InFact,
    ) -> RuntimeResult<Vec<InferAtomicExceptEqualityResult>> {
        let mut rules = Vec::new();
        if let Some(builder) = self.resolve_set_builder_for_membership_projection(&in_fact.set) {
            let mut derived = Vec::new();
            let fact_id = self.ids.allocate_fact_id();
            let base_in = AtomicFact::InFact(InFact {
                fact_id,
                element: in_fact.element.clone(),
                set: builder.param_set.as_ref().clone(),
                line_file: in_fact.line_file.clone(),
            });
            derived.push(self.store_inferred_fact_and_infer(&Fact::AtomicFact(base_in))?);
            let mut subst = std::collections::HashMap::new();
            subst.insert(builder.param_binding.id, in_fact.element.clone());
            for defining in &builder.facts {
                let Ok(qf) = self.inst_quantifier_free_fact(defining, &subst) else {
                    continue;
                };
                let projected = crate::new_pipeline::instantiate::quantifier_free_fact_to_fact(qf);
                derived.push(self.store_inferred_fact_and_infer(&projected)?);
            }
            rules.push(InferAtomicExceptEqualityResult::InFactSetBuilder(
                InferSetBuilderMembershipProjectionResult { derived },
            ));
        }
        if let Some(base) = self.resolve_power_set_base_for_membership_projection(&in_fact.set) {
            let fact_id = self.ids.allocate_fact_id();
            let subset = AtomicFact::SubsetFact(crate::new_pipeline::ast::fact::SubsetFact {
                fact_id,
                left: in_fact.element.clone(),
                right: base,
                line_file: in_fact.line_file.clone(),
            });
            let derived = Box::new(self.store_inferred_fact_and_infer(&Fact::AtomicFact(subset))?);
            rules.push(InferAtomicExceptEqualityResult::InFactPowerSet(
                InferPowerSetMembershipProjectionResult { derived },
            ));
        }
        rules.extend(self.infer_in_fact_standard_set_rules(in_fact)?);
        rules.extend(self.infer_in_fact_list_set_ops_rules(in_fact)?);
        rules.extend(self.infer_in_fact_cart_interval_rules(in_fact)?);
        Ok(rules)
    }
}

impl Runtime {
    fn resolve_set_builder_for_membership_projection(
        &self,
        set: &Obj,
    ) -> Option<crate::new_pipeline::ast::obj::SetBuilder> {
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
