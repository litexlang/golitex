//! Set-construction object WD (children only until P1).

use super::entry::ObjWellDefinedProofByDef;
use crate::new_pipeline::ast::obj::{
    BigIntersect, BigUnion, Cart, CartDim, FiniteSetMax, FiniteSetMin, FiniteSetSize, FnRange,
    GeneralCart, IndexIntersect, IndexUnion, Intersect, IntervalObj, IntervalObjStruct, ListSet,
    OneSideInfinityIntervalObj, PowerSet, Proj, Replacement, SetBuilder, SetMinus, Tuple, TupleDim,
    Union,
};
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

impl Runtime {
    pub(super) fn verify_union_obj_well_definedness_by_def(
        &mut self,
        value: &Union,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
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
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
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
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_binary_obj_well_definedness_by_def(
            value.left.as_ref(),
            value.right.as_ref(),
            verify_state,
        )
    }
    pub(super) fn verify_big_union_obj_well_definedness_by_def(
        &mut self,
        value: &BigUnion,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_unary_obj_well_definedness_by_def(value.left.as_ref(), verify_state)
    }
    pub(super) fn verify_big_intersect_obj_well_definedness_by_def(
        &mut self,
        value: &BigIntersect,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_unary_obj_well_definedness_by_def(value.left.as_ref(), verify_state)
    }
    pub(super) fn verify_index_union_obj_well_definedness_by_def(
        &mut self,
        value: &IndexUnion,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_objs_as_children(
            &[
                value.index_set.as_ref(),
                value.ambient_set.as_ref(),
                value.family_fn.as_ref(),
            ],
            verify_state,
        )
    }
    pub(super) fn verify_index_intersect_obj_well_definedness_by_def(
        &mut self,
        value: &IndexIntersect,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_objs_as_children(
            &[
                value.index_set.as_ref(),
                value.ambient_set.as_ref(),
                value.family_fn.as_ref(),
            ],
            verify_state,
        )
    }
    pub(super) fn verify_power_set_obj_well_definedness_by_def(
        &mut self,
        value: &PowerSet,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_unary_obj_well_definedness_by_def(value.set.as_ref(), verify_state)
    }
    pub(super) fn verify_general_cart_obj_well_definedness_by_def(
        &mut self,
        value: &GeneralCart,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_objs_as_children(
            &[
                value.index_set.as_ref(),
                value.family_set.as_ref(),
                value.family_fn.as_ref(),
            ],
            verify_state,
        )
    }
    pub(super) fn verify_list_set_obj_well_definedness_by_def(
        &mut self,
        value: &ListSet,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_boxed_objs_as_children(&value.list, verify_state)
    }
    pub(super) fn verify_set_builder_obj_well_definedness_by_def(
        &mut self,
        value: &SetBuilder,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        let _ = &value.alpha.facts;
        self.verify_unary_obj_well_definedness_by_def(value.alpha.param_set.as_ref(), verify_state)
    }
    pub(super) fn verify_cart_obj_well_definedness_by_def(
        &mut self,
        value: &Cart,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_boxed_objs_as_children(&value.args, verify_state)
    }
    pub(super) fn verify_cart_dim_obj_well_definedness_by_def(
        &mut self,
        value: &CartDim,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_unary_obj_well_definedness_by_def(value.set.as_ref(), verify_state)
    }
    pub(super) fn verify_proj_obj_well_definedness_by_def(
        &mut self,
        value: &Proj,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_binary_obj_well_definedness_by_def(
            value.set.as_ref(),
            value.dim.as_ref(),
            verify_state,
        )
    }
    pub(super) fn verify_tuple_dim_obj_well_definedness_by_def(
        &mut self,
        value: &TupleDim,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_unary_obj_well_definedness_by_def(value.arg.as_ref(), verify_state)
    }
    pub(super) fn verify_tuple_obj_well_definedness_by_def(
        &mut self,
        value: &Tuple,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_boxed_objs_as_children(&value.args, verify_state)
    }
    pub(super) fn verify_finite_set_size_obj_well_definedness_by_def(
        &mut self,
        value: &FiniteSetSize,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_unary_obj_well_definedness_by_def(value.set.as_ref(), verify_state)
    }
    pub(super) fn verify_finite_set_max_obj_well_definedness_by_def(
        &mut self,
        value: &FiniteSetMax,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_unary_obj_well_definedness_by_def(value.set.as_ref(), verify_state)
    }
    pub(super) fn verify_finite_set_min_obj_well_definedness_by_def(
        &mut self,
        value: &FiniteSetMin,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_unary_obj_well_definedness_by_def(value.set.as_ref(), verify_state)
    }
    pub(super) fn verify_fn_range_obj_well_definedness_by_def(
        &mut self,
        value: &FnRange,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_unary_obj_well_definedness_by_def(value.function.as_ref(), verify_state)
    }
    pub(super) fn verify_replacement_obj_well_definedness_by_def(
        &mut self,
        value: &Replacement,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_unary_obj_well_definedness_by_def(value.source_set.as_ref(), verify_state)
    }
    pub(super) fn verify_one_side_infinity_interval_obj_well_definedness_by_def(
        &mut self,
        value: &OneSideInfinityIntervalObj,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        let start = match value {
            OneSideInfinityIntervalObj::LeftOpen(v)
            | OneSideInfinityIntervalObj::LeftClosed(v)
            | OneSideInfinityIntervalObj::RightOpen(v)
            | OneSideInfinityIntervalObj::RightClosed(v) => v.start.as_ref(),
        };
        self.verify_unary_obj_well_definedness_by_def(start, verify_state)
    }
    pub(super) fn verify_interval_obj_well_definedness_by_def(
        &mut self,
        value: &IntervalObj,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        let bounds: &IntervalObjStruct = match value {
            IntervalObj::LeftOpenRightOpen(v)
            | IntervalObj::LeftOpenRightClosed(v)
            | IntervalObj::LeftClosedRightOpen(v)
            | IntervalObj::LeftClosedRightClosed(v) => v,
        };
        self.verify_binary_obj_well_definedness_by_def(
            bounds.start.as_ref(),
            bounds.end.as_ref(),
            verify_state,
        )
    }
}
