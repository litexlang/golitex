use crate::new_pipeline::ast::fact::{AtomicFact, Fact, InFact};
use crate::new_pipeline::ast::obj::{Obj, SetFormer, SetOperator};
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // When: stored `x $in S` where `S` is (or equals) a set-builder / power_set.
    // Infers: base membership + defining facts, or `x $subset base` for power_set.
    // Example: trust `a $in {x R: x > 0}` also stores `a $in R` and `a > 0`.
    pub(super) fn infer_membership_projection_stage(
        &mut self,
        in_fact: &InFact,
    ) -> RuntimeResult<()> {
        if let Some(builder) = self.resolve_set_builder_for_membership_projection(&in_fact.set) {
            let base_in = AtomicFact::InFact(InFact {
                fact_id: self.ids.allocate_fact_id(),
                element: in_fact.element.clone(),
                set: builder.param_set.as_ref().clone(),
                line_file: in_fact.line_file.clone(),
            });
            self.store_atomic_fact(&base_in)?;
            let mut subst = std::collections::HashMap::new();
            subst.insert(builder.param_binding.id, in_fact.element.clone());
            for defining in &builder.facts {
                let Ok(qf) = self.inst_quantifier_free_fact(defining, &subst) else {
                    continue;
                };
                let projected = crate::new_pipeline::instantiate::quantifier_free_fact_to_fact(qf);
                match projected {
                    Fact::AtomicFact(atomic) => {
                        self.store_atomic_fact(&atomic)?;
                    }
                    other => {
                        let _ = self.store_fact_and_infer(&other)?;
                    }
                }
            }
            return Ok(());
        }
        if let Some(base) = self.resolve_power_set_base_for_membership_projection(&in_fact.set) {
            let subset = AtomicFact::SubsetFact(crate::new_pipeline::ast::fact::SubsetFact {
                fact_id: self.ids.allocate_fact_id(),
                left: in_fact.element.clone(),
                right: base,
                line_file: in_fact.line_file.clone(),
            });
            self.store_atomic_fact(&subset)?;
        }
        Ok(())
    }

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
