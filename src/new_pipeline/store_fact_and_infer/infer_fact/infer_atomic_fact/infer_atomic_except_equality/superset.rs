use crate::new_pipeline::ast::fact::{
    AtomicFact, ExistOrAndChainAtomicFact, Fact, ForallFact, InFact, SupersetFact,
};
use crate::new_pipeline::ast::obj::{IdentifierObj, Obj};
use crate::new_pipeline::ast::param::{ParamType, TypedParameterGroup, TypedParameterList};
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};
use crate::new_pipeline::store_fact_and_infer::InferSupersetElementwiseMembershipResult;

impl Runtime {
    // When: stored `A $superset B`.
    // Infers: `forall x B: x $in A`.
    pub(super) fn infer_superset_elementwise_membership(
        &mut self,
        superset: &SupersetFact,
    ) -> RuntimeResult<InferSupersetElementwiseMembershipResult> {
        let binder = self.fresh_internal_param();
        let forall = ForallFact {
            fact_id: self.global_ids.allocate_fact_id(),
            typed_parameters: TypedParameterList {
                groups: vec![TypedParameterGroup {
                    params: vec![binder.clone()],
                    param_type: ParamType::Obj(superset.right.clone()),
                }],
            },
            dom_facts: Vec::new(),
            then_facts: vec![ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::InFact(
                InFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    element: Obj::Identifier(IdentifierObj::from_bound_name(&binder)),
                    set: superset.left.clone(),
                    line_file: superset.line_file.clone(),
                },
            ))],
            line_file: superset.line_file.clone(),
        };
        let derived = Box::new(self.store_inferred_fact_and_infer(&Fact::ForallFact(forall))?);
        Ok(InferSupersetElementwiseMembershipResult { derived })
    }
}
