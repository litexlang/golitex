use crate::new_pipeline::ast::fact::{
    AtomicFact, ExistOrAndChainAtomicFact, Fact, ForallFact, InFact, SubsetFact,
};
use crate::new_pipeline::ast::obj::{IdentifierObj, Obj, SetFormer};
use crate::new_pipeline::ast::param::{ParamType, TypedParameterGroup, TypedParameterList};
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};
use crate::new_pipeline::store_fact_and_infer::InferSubsetElementwiseMembershipResult;

impl Runtime {
    // When: stored `A $subset B` and A is not (equal to) a set-builder.
    // Infers: `forall x A: x $in B`.
    pub(super) fn infer_subset_elementwise_membership(
        &mut self,
        subset: &SubsetFact,
    ) -> RuntimeResult<Option<InferSubsetElementwiseMembershipResult>> {
        if self.set_is_or_equals_set_builder(&subset.left) {
            return Ok(None);
        }
        let binder = self.fresh_internal_param();
        let forall = ForallFact {
            fact_id: self.ids.allocate_fact_id(),
            typed_parameters: TypedParameterList {
                groups: vec![TypedParameterGroup {
                    params: vec![binder.clone()],
                    param_type: ParamType::Obj(subset.left.clone()),
                }],
            },
            dom_facts: Vec::new(),
            then_facts: vec![ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::InFact(
                InFact {
                    fact_id: self.ids.allocate_fact_id(),
                    element: Obj::Identifier(IdentifierObj::from_bound_name(&binder)),
                    set: subset.right.clone(),
                    line_file: subset.line_file.clone(),
                },
            ))],
            line_file: subset.line_file.clone(),
        };
        let derived = Box::new(self.store_inferred_fact_and_infer(&Fact::ForallFact(forall))?);
        Ok(Some(InferSubsetElementwiseMembershipResult { derived }))
    }

    fn set_is_or_equals_set_builder(&self, set: &Obj) -> bool {
        if matches!(set, Obj::SetFormer(SetFormer::SetBuilder(_))) {
            return true;
        }
        let adjacency = self.visible_equivalence_class_adjacency();
        let Some(neighbors) = adjacency.get(&set.ir()) else {
            return false;
        };
        for (_peer_key, equal_fact) in neighbors.iter() {
            let peer = if equal_fact.left.ir() == set.ir() {
                &equal_fact.right
            } else {
                &equal_fact.left
            };
            if matches!(peer, Obj::SetFormer(SetFormer::SetBuilder(_))) {
                return true;
            }
        }
        false
    }
}
