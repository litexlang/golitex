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
        if self
            .resolve_set_builder_for_membership_projection(&in_fact.set)
            .is_some()
        {
            let mut derived = Vec::new();
            let mut pending = vec![in_fact.clone()];
            let mut expanded = std::collections::HashSet::new();
            while let Some(member) = pending.pop() {
                if !expanded.insert(member.ir()) {
                    continue;
                }
                let Some(builder) = self.resolve_set_builder_for_membership_projection(&member.set)
                else {
                    continue;
                };
                let base_in = InFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    element: member.element.clone(),
                    set: builder.param_set.as_ref().clone(),
                    line_file: member.line_file.clone(),
                };
                pending.push(base_in.clone());
                self.store_new_set_builder_projection(
                    &Fact::AtomicFact(AtomicFact::InFact(base_in)),
                    verify_state,
                    &mut derived,
                )?;
                let mut subst = std::collections::HashMap::new();
                subst.insert(builder.param_binding.id, member.element.clone());
                for defining in &builder.facts {
                    let Ok(qf) = self.inst_quantifier_free_fact(defining, &subst) else {
                        continue;
                    };
                    let projected = crate::instantiate::quantifier_free_fact_to_fact(qf);
                    // A visible membership may predate a builder equality. Its
                    // newly available carrier conditions still need projection.
                    let atomics = match &projected {
                        Fact::AtomicFact(atomic) => vec![atomic.clone()],
                        Fact::AndFact(and) => and.facts.clone(),
                        Fact::ChainFact(chain) => self.chain_adjacent_atomics(chain)?,
                        _ => Vec::new(), // An Or does not establish either branch.
                    };
                    pending.extend(atomics.into_iter().filter_map(|atomic| match atomic {
                        AtomicFact::InFact(member) => Some(member),
                        _ => None,
                    }));
                    self.store_new_set_builder_projection(&projected, verify_state, &mut derived)?;
                }
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
        if let Some(rule) = self.infer_in_fact_preimage(in_fact, verify_state)? {
            rules.push(rule);
        }
        rules.extend(self.infer_in_fact_fn_rules(in_fact, verify_state)?);
        rules.extend(self.infer_in_fact_index_family_rules(in_fact, verify_state)?);
        Ok(rules)
    }
}

impl Runtime {
    // The source membership is stored before inference. A builder reached
    // through equality can project that same membership (or cycle through a
    // second carrier). Skip repeated storage, while the local projection queue
    // still visits known carriers whose defining conditions arrived later.
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
        for (value, _) in self.exact_property_object_values(set) {
            if let Obj::SetFormer(SetFormer::SetBuilder(builder)) = value {
                return Some(builder);
            }
        }
        None
    }

    fn resolve_power_set_base_for_membership_projection(&self, set: &Obj) -> Option<Obj> {
        if let Obj::SetOperator(SetOperator::PowerSet(power)) = set {
            return Some(power.set.as_ref().clone());
        }
        for (value, _) in self.exact_property_object_values(set) {
            if let Obj::SetOperator(SetOperator::PowerSet(power)) = value {
                return Some(*power.set);
            }
        }
        None
    }
}

#[cfg(test)]
#[path = "../../../../../tests/unit/execute/set_builder_projection_cycle/tests.rs"]
mod set_builder_projection_cycle_tests;
