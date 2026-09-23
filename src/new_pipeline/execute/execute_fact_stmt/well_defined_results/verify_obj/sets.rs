//! Set-construction object WD.
//! Light legacy requirements: CartDim/Proj/TupleDim, ListSet pairwise !=,
//! FiniteSetSize/Max/Min, Interval/Ray in R, Index*/IndexCart `$is_set` +
//! family ∈ FnSet (registration half). Union/PowerSet/Cart/Tuple stay children-only.

use super::entry::{ObjWellDefinedProof, VerifyObjWellDefinedResult};
use super::fail_to_verify_obj_well_defined::*;
use super::obj_well_defined_by_def_common::ObjWellDefinedByDefCommonStages;
use super::obj_well_defined_proof_by_def::*;
use crate::new_pipeline::ast::fact::{
    AtomicFact, IsCartFact, IsTupleFact, LessEqualFact, NotEqualFact,
};
use crate::new_pipeline::ast::obj::{
    FamilyIntersect, FamilyUnion, Cart, CartDim, FiniteSetMax, FiniteSetMin, FiniteSetSize,
    IndexCart, IndexIntersect, IndexUnion, Intersect, IntervalObj, IntervalObjStruct, ListSet, Obj,
    OneSideInfinityIntervalObj, PowerSet, ProductShape, Proj, SetMinus, SetOperator, StandardSet,
    Tuple, TupleDim, Union,
};
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

impl Runtime {
    pub(super) fn verify_union_obj_well_definedness_by_def(
        &mut self,
        value: &Union,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        self.verify_binary_obj_well_definedness_by_def(
            value.left.as_ref(),
            value.right.as_ref(),
            verify_state,
        )
    }
    pub(super) fn verify_intersect_obj_well_definedness_by_def(
        &mut self,
        value: &Intersect,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        self.verify_binary_obj_well_definedness_by_def(
            value.left.as_ref(),
            value.right.as_ref(),
            verify_state,
        )
    }
    pub(super) fn verify_set_minus_obj_well_definedness_by_def(
        &mut self,
        value: &SetMinus,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        self.verify_binary_obj_well_definedness_by_def(
            value.left.as_ref(),
            value.right.as_ref(),
            verify_state,
        )
    }
    pub(super) fn verify_family_union_obj_well_definedness_by_def(
        &mut self,
        value: &FamilyUnion,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        self.verify_unary_obj_well_definedness_by_def(value.left.as_ref(), verify_state)
    }
    pub(super) fn verify_family_intersect_obj_well_definedness_by_def(
        &mut self,
        value: &FamilyIntersect,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        self.verify_unary_obj_well_definedness_by_def(value.left.as_ref(), verify_state)
    }
    // index_union(I, X, A): children, `$is_set(I)`, `$is_set(X)`, then A ∈ some FnSet.
    // Example: after `let A = fn(k {1}) power_set(N) {{1}}`, `index_union({1}, N, A)` is WD.
    // Full legacy also checks `A $in fn(k I) power_set(X)` (deferred).
    pub(super) fn verify_index_union_obj_well_definedness(
        &mut self,
        value: &IndexUnion,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyObjWellDefinedResult> {
        let stages = self.verify_index_union_obj_well_definedness_by_def(value, verify_state.clone())?;
        if !stages.is_fully_known() {
            return Ok(VerifyObjWellDefinedResult::Failed(
                FailToVerifyObjWellDefinedResult::SetOperator(FailToVerifySetOperatorObjWellDefinedResult::IndexUnion(
                    FailToVerifyIndexUnionObjWellDefined::Domain(
                        stages.into_common_fail(&Obj::SetOperator(SetOperator::IndexUnion(value.clone()))),
                    ),
                )),
            ));
        }
        if !self.obj_has_in_function_set(value.family_fn.as_ref()) {
            return Ok(VerifyObjWellDefinedResult::Failed(
                FailToVerifyObjWellDefinedResult::SetOperator(FailToVerifySetOperatorObjWellDefinedResult::IndexUnion(
                    FailToVerifyIndexUnionObjWellDefined::NotInFunctionSet,
                )),
            ));
        }
        if verify_state.store_well_defined_fact {
            let wd_id = self.ids.allocate_well_definedness_id();
            self.top_exec_env_mut()
                .well_defined_objects
                .record(Obj::SetOperator(SetOperator::IndexUnion(value.clone())), wd_id);
        }
        Ok(VerifyObjWellDefinedResult::Success(ObjWellDefinedProof::ByDef(
            ObjWellDefinedProofByDef::SetOperator(SetOperatorObjWellDefinedProofByDef::IndexUnion(IndexUnionObjWellDefinedProof::from_stages(stages))),
        )))
    }

    fn verify_index_union_obj_well_definedness_by_def(
        &mut self,
        value: &IndexUnion,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        let proof = self.verify_objs_as_children(
            &[
                value.index_set.as_ref(),
                value.ambient_set.as_ref(),
                value.family_fn.as_ref(),
            ],
            verify_state.clone(),
        )?;
        let mut reqs = Vec::new();
        reqs.push(self.require_is_set(
            value.index_set.as_ref(),
            verify_state.clone(),
            format!("index_union: index {} is not a set", value.index_set.ir()),
        )?);
        reqs.push(self.require_is_set(
            value.ambient_set.as_ref(),
            verify_state,
            format!("index_union: ambient {} is not a set", value.ambient_set.ir()),
        )?);
        Ok(self.with_requirements(proof, reqs))
    }

    // index_intersect: same `$is_set` + family ∈ FnSet half as index_union.
    pub(super) fn verify_index_intersect_obj_well_definedness(
        &mut self,
        value: &IndexIntersect,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyObjWellDefinedResult> {
        let stages =
            self.verify_index_intersect_obj_well_definedness_by_def(value, verify_state.clone())?;
        if !stages.is_fully_known() {
            return Ok(VerifyObjWellDefinedResult::Failed(
                FailToVerifyObjWellDefinedResult::SetOperator(FailToVerifySetOperatorObjWellDefinedResult::IndexIntersect(
                    FailToVerifyIndexIntersectObjWellDefined::Domain(
                        stages.into_common_fail(&Obj::SetOperator(SetOperator::IndexIntersect(value.clone()))),
                    ),
                )),
            ));
        }
        if !self.obj_has_in_function_set(value.family_fn.as_ref()) {
            return Ok(VerifyObjWellDefinedResult::Failed(
                FailToVerifyObjWellDefinedResult::SetOperator(FailToVerifySetOperatorObjWellDefinedResult::IndexIntersect(
                    FailToVerifyIndexIntersectObjWellDefined::NotInFunctionSet,
                )),
            ));
        }
        if verify_state.store_well_defined_fact {
            let wd_id = self.ids.allocate_well_definedness_id();
            self.top_exec_env_mut()
                .well_defined_objects
                .record(Obj::SetOperator(SetOperator::IndexIntersect(value.clone())), wd_id);
        }
        Ok(VerifyObjWellDefinedResult::Success(ObjWellDefinedProof::ByDef(
            ObjWellDefinedProofByDef::SetOperator(SetOperatorObjWellDefinedProofByDef::IndexIntersect(
                IndexIntersectObjWellDefinedProof::from_stages(stages),
            )),
        )))
    }

    fn verify_index_intersect_obj_well_definedness_by_def(
        &mut self,
        value: &IndexIntersect,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        let proof = self.verify_objs_as_children(
            &[
                value.index_set.as_ref(),
                value.ambient_set.as_ref(),
                value.family_fn.as_ref(),
            ],
            verify_state.clone(),
        )?;
        let mut reqs = Vec::new();
        reqs.push(self.require_is_set(
            value.index_set.as_ref(),
            verify_state.clone(),
            format!(
                "index_intersect: index {} is not a set",
                value.index_set.ir()
            ),
        )?);
        reqs.push(self.require_is_set(
            value.ambient_set.as_ref(),
            verify_state,
            format!(
                "index_intersect: ambient {} is not a set",
                value.ambient_set.ir()
            ),
        )?);
        Ok(self.with_requirements(proof, reqs))
    }
    pub(super) fn verify_power_set_obj_well_definedness_by_def(
        &mut self,
        value: &PowerSet,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        self.verify_unary_obj_well_definedness_by_def(value.set.as_ref(), verify_state)
    }
    // index_cart(I, S, g): children, `$is_set(I)`, `$is_nonempty_set(S)`, then g ∈ FnSet.
    // Example: after `let g = fn(alpha {1}) power_set(N) {{1}}`, `index_cart({1}, power_set(N), g)` is WD.
    // Full legacy also checks `g $in fn(alpha I) S` (deferred).
    pub(super) fn verify_index_cart_obj_well_definedness(
        &mut self,
        value: &IndexCart,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyObjWellDefinedResult> {
        let stages =
            self.verify_index_cart_obj_well_definedness_by_def(value, verify_state.clone())?;
        if !stages.is_fully_known() {
            return Ok(VerifyObjWellDefinedResult::Failed(
                FailToVerifyObjWellDefinedResult::SetOperator(FailToVerifySetOperatorObjWellDefinedResult::IndexCart(
                    FailToVerifyIndexCartObjWellDefined::Domain(
                        stages.into_common_fail(&Obj::SetOperator(SetOperator::IndexCart(value.clone()))),
                    ),
                )),
            ));
        }
        if !self.obj_has_in_function_set(value.family_fn.as_ref()) {
            return Ok(VerifyObjWellDefinedResult::Failed(
                FailToVerifyObjWellDefinedResult::SetOperator(FailToVerifySetOperatorObjWellDefinedResult::IndexCart(
                    FailToVerifyIndexCartObjWellDefined::NotInFunctionSet,
                )),
            ));
        }
        if verify_state.store_well_defined_fact {
            let wd_id = self.ids.allocate_well_definedness_id();
            self.top_exec_env_mut()
                .well_defined_objects
                .record(Obj::SetOperator(SetOperator::IndexCart(value.clone())), wd_id);
        }
        Ok(VerifyObjWellDefinedResult::Success(ObjWellDefinedProof::ByDef(
            ObjWellDefinedProofByDef::SetOperator(SetOperatorObjWellDefinedProofByDef::IndexCart(IndexCartObjWellDefinedProof::from_stages(
                stages,
            ))),
        )))
    }

    fn verify_index_cart_obj_well_definedness_by_def(
        &mut self,
        value: &IndexCart,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        let proof = self.verify_objs_as_children(
            &[
                value.index_set.as_ref(),
                value.family_set.as_ref(),
                value.family_fn.as_ref(),
            ],
            verify_state.clone(),
        )?;
        let mut reqs = Vec::new();
        reqs.push(self.require_is_set(
            value.index_set.as_ref(),
            verify_state.clone(),
            format!(
                "index_cart: index {} is not a set",
                value.index_set.ir()
            ),
        )?);
        reqs.push(self.require_is_nonempty_set(
            value.family_set.as_ref(),
            verify_state,
            format!(
                "index_cart: family {} is not a nonempty set",
                value.family_set.ir()
            ),
        )?);
        Ok(self.with_requirements(proof, reqs))
    }

    // list set: children, then pairwise != among elements.
    // Example: `{1, 2}` needs `1 != 2`.
    pub(super) fn verify_list_set_obj_well_definedness_by_def(
        &mut self,
        value: &ListSet,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        let proof = self.verify_boxed_objs_as_children(&value.list, verify_state.clone())?;
        let mut reqs = Vec::new();
        for left_index in 0..value.list.len() {
            for right_index in (left_index + 1)..value.list.len() {
                let not_eq = AtomicFact::NotEqualFact(NotEqualFact {
                    fact_id: self.ids.allocate_fact_id(),
                    left: value.list[left_index].as_ref().clone(),
                    right: value.list[right_index].as_ref().clone(),
                    line_file: None,
                });
                reqs.push(self.verify_required_atomic_fact(
                    not_eq,
                    verify_state.clone(),
                    "list set elements must be pairwise not equal".to_string(),
                )?);
            }
        }
        Ok(self.with_requirements(proof, reqs))
    }
    // SetBuilder: dedicated binder pipeline in binder.rs.
    pub(super) fn verify_cart_obj_well_definedness_by_def(
        &mut self,
        value: &Cart,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        self.verify_boxed_objs_as_children(&value.args, verify_state)
    }
    // cart_dim(S): children, then `$is_cart(S)`.
    // Example: `cart_dim(cart(R, R))` needs `$is_cart(cart(R, R))`.
    pub(super) fn verify_cart_dim_obj_well_definedness_by_def(
        &mut self,
        value: &CartDim,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        let proof = self
            .verify_unary_obj_well_definedness_by_def(value.set.as_ref(), verify_state.clone())?;
        let is_cart = AtomicFact::IsCartFact(IsCartFact {
            fact_id: self.ids.allocate_fact_id(),
            set: value.set.as_ref().clone(),
            line_file: None,
        });
        let req = self.verify_required_atomic_fact(
            is_cart,
            verify_state,
            format!("set {} is not a cart", value.set.ir()),
        )?;
        Ok(self.with_requirements(proof, vec![req]))
    }

    // proj(S, i): children, then `i $in N+`, `$is_cart(S)`, `i <= cart_dim(S)`.
    // Example: `proj(cart(R, R), 1)` is WD; `proj(R, 1)` fails `$is_cart`.
    pub(super) fn verify_proj_obj_well_definedness_by_def(
        &mut self,
        value: &Proj,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        let proof = self.verify_binary_obj_well_definedness_by_def(
            value.set.as_ref(),
            value.dim.as_ref(),
            verify_state.clone(),
        )?;
        let mut reqs = Vec::new();
        reqs.push(self.require_obj_in_standard_set(
            value.dim.as_ref(),
            StandardSet::NPos,
            verify_state.clone(),
            format!(
                "projection dimension {} is not a positive integer",
                value.dim.ir()
            ),
        )?);
        let is_cart = AtomicFact::IsCartFact(IsCartFact {
            fact_id: self.ids.allocate_fact_id(),
            set: value.set.as_ref().clone(),
            line_file: None,
        });
        reqs.push(self.verify_required_atomic_fact(
            is_cart,
            verify_state.clone(),
            format!("projection left side {} is not a cart", value.set.ir()),
        )?);
        let cart_dim: Obj = Obj::ProductShape(ProductShape::CartDim(CartDim {
            set: value.set.clone(),
        }));
        let bounded = AtomicFact::LessEqualFact(LessEqualFact {
            fact_id: self.ids.allocate_fact_id(),
            left: value.dim.as_ref().clone(),
            right: cart_dim.clone(),
            line_file: None,
        });
        reqs.push(self.verify_required_atomic_fact(
            bounded,
            verify_state,
            format!("{} <= {} is unknown", value.dim.ir(), cart_dim.ir()),
        )?);
        Ok(self.with_requirements(proof, reqs))
    }

    // tuple_dim(t): children, then `$is_tuple(t)`.
    // Example: `tuple_dim((1, 2))` needs `$is_tuple((1, 2))`.
    pub(super) fn verify_tuple_dim_obj_well_definedness_by_def(
        &mut self,
        value: &TupleDim,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        let proof = self
            .verify_unary_obj_well_definedness_by_def(value.arg.as_ref(), verify_state.clone())?;
        let is_tuple = AtomicFact::IsTupleFact(IsTupleFact {
            fact_id: self.ids.allocate_fact_id(),
            set: value.arg.as_ref().clone(),
            line_file: None,
        });
        let req = self.verify_required_atomic_fact(
            is_tuple,
            verify_state,
            format!(
                "`$is_tuple({})` is unknown, `dim` object requires its argument to be a tuple",
                value.arg.ir()
            ),
        )?;
        Ok(self.with_requirements(proof, vec![req]))
    }
    pub(super) fn verify_tuple_obj_well_definedness_by_def(
        &mut self,
        value: &Tuple,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        self.verify_boxed_objs_as_children(&value.args, verify_state)
    }
    // finite_set_size(S): children, then `$is_finite_set(S)`.
    // Example: `finite_set_size({1, 2})`.
    pub(super) fn verify_finite_set_size_obj_well_definedness_by_def(
        &mut self,
        value: &FiniteSetSize,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        let proof = self
            .verify_unary_obj_well_definedness_by_def(value.set.as_ref(), verify_state.clone())?;
        let req = self.require_is_finite_set(
            value.set.as_ref(),
            verify_state,
            format!("set {} is not a finite set", value.set.ir()),
        )?;
        Ok(self.with_requirements(proof, vec![req]))
    }

    // finite_set_max(S): children, `$is_finite_set` and `$is_nonempty_set`.
    pub(super) fn verify_finite_set_max_obj_well_definedness_by_def(
        &mut self,
        value: &FiniteSetMax,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        let proof = self
            .verify_unary_obj_well_definedness_by_def(value.set.as_ref(), verify_state.clone())?;
        let mut reqs = Vec::new();
        reqs.push(self.require_is_finite_set(
            value.set.as_ref(),
            verify_state.clone(),
            format!("finite_set_max requires a finite nonempty set, got {}", value.set.ir()),
        )?);
        reqs.push(self.require_is_nonempty_set(
            value.set.as_ref(),
            verify_state,
            format!("finite_set_max requires a finite nonempty set, got {}", value.set.ir()),
        )?);
        Ok(self.with_requirements(proof, reqs))
    }

    // finite_set_min(S): same as max.
    pub(super) fn verify_finite_set_min_obj_well_definedness_by_def(
        &mut self,
        value: &FiniteSetMin,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        let proof = self
            .verify_unary_obj_well_definedness_by_def(value.set.as_ref(), verify_state.clone())?;
        let mut reqs = Vec::new();
        reqs.push(self.require_is_finite_set(
            value.set.as_ref(),
            verify_state.clone(),
            format!("finite_set_min requires a finite nonempty set, got {}", value.set.ir()),
        )?);
        reqs.push(self.require_is_nonempty_set(
            value.set.as_ref(),
            verify_state,
            format!("finite_set_min requires a finite nonempty set, got {}", value.set.ir()),
        )?);
        Ok(self.with_requirements(proof, reqs))
    }

    // one-sided ray: endpoint WD + endpoint $in R.
    pub(super) fn verify_one_side_infinity_interval_obj_well_definedness_by_def(
        &mut self,
        value: &OneSideInfinityIntervalObj,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        let start = match value {
            OneSideInfinityIntervalObj::LeftOpen(v)
            | OneSideInfinityIntervalObj::LeftClosed(v)
            | OneSideInfinityIntervalObj::RightOpen(v)
            | OneSideInfinityIntervalObj::RightClosed(v) => v.start.as_ref(),
        };
        let proof = self.verify_unary_obj_well_definedness_by_def(start, verify_state.clone())?;
        let req = self.require_obj_in_standard_set(
            start,
            StandardSet::R,
            verify_state,
            format!("ray endpoint {} is not in R", start.ir()),
        )?;
        Ok(self.with_requirements(proof, vec![req]))
    }

    // interval [a,b] variants: both endpoints WD + $in R.
    pub(super) fn verify_interval_obj_well_definedness_by_def(
        &mut self,
        value: &IntervalObj,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        let bounds: &IntervalObjStruct = match value {
            IntervalObj::LeftOpenRightOpen(v)
            | IntervalObj::LeftOpenRightClosed(v)
            | IntervalObj::LeftClosedRightOpen(v)
            | IntervalObj::LeftClosedRightClosed(v) => v,
        };
        let proof = self.verify_binary_obj_well_definedness_by_def(
            bounds.start.as_ref(),
            bounds.end.as_ref(),
            verify_state.clone(),
        )?;
        let mut reqs = Vec::new();
        reqs.push(self.require_obj_in_standard_set(
            bounds.start.as_ref(),
            StandardSet::R,
            verify_state.clone(),
            format!("interval start {} is not in R", bounds.start.ir()),
        )?);
        reqs.push(self.require_obj_in_standard_set(
            bounds.end.as_ref(),
            StandardSet::R,
            verify_state,
            format!("interval end {} is not in R", bounds.end.ir()),
        )?);
        Ok(self.with_requirements(proof, reqs))
    }
}

