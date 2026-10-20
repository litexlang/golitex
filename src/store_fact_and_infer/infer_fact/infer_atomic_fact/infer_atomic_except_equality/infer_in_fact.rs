use crate::ast::fact::{AtomicFact, Fact, InFact};
use crate::ast::obj::{Obj, SetFormer, SetOperator};
use crate::prelude::*;
use crate::runtime::{Runtime, RuntimeResult};
use crate::store_fact_and_infer::{
    InferInFactResult, InferPowerSetMembershipProjectionResult,
    InferSetBuilderMembershipProjectionResult, SetBuilderMembershipProjectionStep,
};

impl Runtime {
    // Collect every InFact membership infer rule that fires (may be several families).
    pub(in crate::store_fact_and_infer) fn infer_in_fact(
        &mut self,
        in_fact: &InFact,
        verify_state: crate::execute::execute_fact_stmt::VerifyState,
    ) -> RuntimeResult<Vec<InferInFactResult>> {
        let expansions = self.expand_template_membership(in_fact)?;
        // Retain rules supplied by properties of the surface carrier as well
        // as those supplied by its declaration-owned native definition.
        let mut rules = self.infer_native_in_fact(in_fact, verify_state)?;
        if let Some(native) = expansions.last() {
            let mut stores = Vec::new();
            for expanded in &expansions {
                stores.push(
                    self.store_inferred_fact(&Fact::AtomicFact(AtomicFact::InFact(
                        expanded.clone(),
                    )))?,
                );
            }
            // This is one inference pass on the declaration-normalized seed,
            // not recursive inference on arbitrary derived conclusions.
            let native_rules = self.infer_native_in_fact(native, verify_state)?;
            rules.push(InferInFactResult::Template(
                crate::store_fact_and_infer::InferTemplateMembershipResult {
                    source_fact_id: in_fact.fact_id,
                    expansions,
                    stores,
                    native_rules,
                },
            ));
        }
        Ok(rules)
    }

    fn infer_native_in_fact(
        &mut self,
        in_fact: &InFact,
        verify_state: crate::execute::execute_fact_stmt::VerifyState,
    ) -> RuntimeResult<Vec<InferInFactResult>> {
        let mut rules = Vec::new();
        if let Some((builder, equality_path, template_expansion)) =
            self.resolve_set_builder_for_membership_projection(&in_fact.set, verify_state)?
        {
            let mut steps = Vec::new();
            {
                let member = in_fact.clone();
                let mut projections = Vec::new();
                let base_in = InFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    element: member.element.clone(),
                    set: builder.param_set.as_ref().clone(),
                    line_file: member.line_file.clone(),
                };
                if let Some(stored) = self.store_new_set_builder_projection(&Fact::AtomicFact(
                    AtomicFact::InFact(base_in),
                ))? {
                    projections.push(crate::store_fact_and_infer::InferSetBuilderProjectionResult::BaseMembership(stored));
                }
                let mut subst = std::collections::HashMap::new();
                subst.insert(builder.param_binding.id, member.element.clone());
                for (condition_index, defining) in builder.facts.iter().enumerate() {
                    let Ok(qf) = self.inst_quantifier_free_fact(defining, &subst) else {
                        continue;
                    };
                    let projected = crate::instantiate::quantifier_free_fact_to_fact(qf);
                    if let Some(stored) = self.store_new_set_builder_projection(&projected)? {
                        projections.push(crate::store_fact_and_infer::InferSetBuilderProjectionResult::Condition { condition_index, stored });
                    }
                }
                steps.push(SetBuilderMembershipProjectionStep {
                    source_membership: member,
                    builder,
                    equality_path,
                    template_expansion,
                    projections,
                });
            }
            rules.push(InferInFactResult::SetBuilder(
                InferSetBuilderMembershipProjectionResult { steps },
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
            let derived = Box::new(self.store_inferred_fact(&Fact::AtomicFact(subset))?);
            rules.push(InferInFactResult::PowerSet(
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
    // second carrier). Skip repeated storage; a later explicit membership
    // statement can project newly available carrier conditions.
    // This guard belongs to this projection rule, not to truth search/store.
    pub(super) fn store_new_set_builder_projection(
        &mut self,
        projected: &Fact,
    ) -> RuntimeResult<Option<crate::store_fact_and_infer::StoreInferredFactResult>> {
        let key = projected.ir();
        let already_stored = self.execution_environments_stack.iter().rev().any(|env| {
            env.facts.facts_by_id.values().any(|known| {
                std::mem::discriminant(known) == std::mem::discriminant(projected)
                    && known.ir() == key
            })
        });
        if already_stored {
            return Ok(None);
        }
        Ok(Some(self.store_inferred_fact(projected)?))
    }

    fn resolve_set_builder_for_membership_projection(
        &mut self,
        set: &Obj,
        _verify_state: crate::execute::execute_fact_stmt::VerifyState,
    ) -> RuntimeResult<
        Option<(
            crate::ast::obj::SetBuilder,
            Vec<(Obj, Obj, crate::runtime::FactId)>,
            bool,
        )>,
    > {
        if let Obj::SetFormer(SetFormer::SetBuilder(builder)) = set {
            return Ok(Some((builder.clone(), Vec::new(), false)));
        }
        for (value, equality_path) in self.exact_property_object_values_of_shapes(
            set,
            &[
                EqualToObjShape::SetBuilder,
                EqualToObjShape::InstantiatedTemplateObj,
            ],
        ) {
            if let Obj::SetFormer(SetFormer::SetBuilder(builder)) = &value {
                return Ok(Some((builder.clone(), equality_path, false)));
            }
            // The checked source membership already certifies the template's
            // arguments and guards. Substitute its definition-owned RHS directly;
            // no repeated WD or generic theorem search is needed here.
            if let Obj::InstantiatedTemplateObj(instance) = &value {
                if let Some(Obj::SetFormer(SetFormer::SetBuilder(builder))) =
                    self.expanded_have_obj_equal_rhs_of_instantiated_template(instance)?
                {
                    return Ok(Some((builder, equality_path, true)));
                }
            }
        }
        Ok(None)
    }

    fn resolve_power_set_base_for_membership_projection(&self, set: &Obj) -> Option<Obj> {
        if let Obj::SetOperator(SetOperator::PowerSet(power)) = set {
            return Some(power.set.as_ref().clone());
        }
        for (value, _) in
            self.exact_property_object_values_of_shapes(set, &[EqualToObjShape::PowerSet])
        {
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
