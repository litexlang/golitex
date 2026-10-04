use crate::ast::fact::{
    AtomicFact, ExistOrAndChainAtomicFact, Fact, ForallFact, InFact, IsFiniteSetFact, SubsetFact,
};
use crate::ast::obj::{IdentifierObj, Obj, SetFormer};
use crate::ast::param::{ParamType, TypedParameterGroup, TypedParameterList};
use crate::runtime::{Runtime, RuntimeResult};
use crate::store_fact_and_infer::{InferSubsetElementwiseMembershipResult, InferSubsetFiniteUpperBoundResult};
use crate::execute::execute_fact_stmt::{VerifyState, VerifyStateLevel};

impl Runtime {
    // A stored inclusion with an already available finite upper bound publishes
    // the lower set's finiteness before a later cardinality WD check.
    // Example: A subset B, B finite_set => is_finite_set(A).
    // Restrict the upper premise to stored/structural evidence; do not recurse
    // through inclusion strategies or reset the caller's search permissions.
    pub(super) fn infer_subset_finite_upper_bound(
        &mut self,
        subset: &SubsetFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<InferSubsetFiniteUpperBoundResult>> {
        let upper_finite: Fact = IsFiniteSetFact {
            fact_id: self.global_ids.allocate_fact_id(),
            set: subset.right.clone(),
            line_file: subset.line_file.clone(),
        }.into();
        let upper_finite_proof = self.verify_fact(
            &upper_finite,
            verify_state.capped_at(VerifyStateLevel::KnownSpecialProperty),
        )?;
        if upper_finite_proof.is_failed() {
            return Ok(None);
        }
        let finite: Fact = IsFiniteSetFact {
            fact_id: self.global_ids.allocate_fact_id(),
            set: subset.left.clone(),
            line_file: subset.line_file.clone(),
        }.into();
        let derived = Box::new(self.store_inferred_fact_and_infer(&finite, verify_state)?);
        Ok(Some(InferSubsetFiniteUpperBoundResult {
            source_fact_id: subset.fact_id,
            upper_finite_proof,
            derived,
        }))
    }
    // When: stored `A $subset B` and A is not (equal to) a set-builder.
    // Infers: `forall x A: x $in B`.
    pub(super) fn infer_subset_elementwise_membership(
        &mut self,
        subset: &SubsetFact,
     verify_state: crate::execute::execute_fact_stmt::VerifyState) -> RuntimeResult<Option<InferSubsetElementwiseMembershipResult>> {
        if self.set_is_or_equals_set_builder(&subset.left) {
            return Ok(None);
        }
        let binder = self.fresh_internal_param();
        let forall = ForallFact {
            fact_id: self.global_ids.allocate_fact_id(),
            typed_parameters: TypedParameterList {
                groups: vec![TypedParameterGroup {
                    params: vec![binder.clone()],
                    param_type: ParamType::Obj(subset.left.clone()),
                }],
            },
            dom_facts: Vec::new(),
            then_facts: vec![ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::InFact(
                InFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    element: Obj::Identifier(IdentifierObj::from_bound_name(&binder)),
                    set: subset.right.clone(),
                    line_file: subset.line_file.clone(),
                },
            ))],
            line_file: subset.line_file.clone(),
        };
        let derived = Box::new(self.store_inferred_fact_and_infer(&Fact::ForallFact(forall), verify_state)?);
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
