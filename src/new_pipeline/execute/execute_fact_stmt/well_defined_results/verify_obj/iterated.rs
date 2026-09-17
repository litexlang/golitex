//! Iterated / range / sequence object WD (children only until P3).

use super::entry::ObjWellDefinedProofByDef;
use crate::new_pipeline::ast::obj::{
    ClosedRange, FiniteSeqListObj, FiniteSeqSet, FiniteSetReduce, ObjAtIndex, Product,
    ProductOfFiniteSet, Range, Reduce, SeqSet, Sum, SumOfFiniteSet,
};
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

impl Runtime {
    pub(super) fn verify_sum_obj_well_definedness_by_def(
        &mut self,
        value: &Sum,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_objs_as_children(
            &[
                value.start.as_ref(),
                value.end.as_ref(),
                value.func.as_ref(),
            ],
            verify_state,
        )
    }
    pub(super) fn verify_sum_of_finite_set_obj_well_definedness_by_def(
        &mut self,
        value: &SumOfFiniteSet,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_binary_obj_well_definedness_by_def(
            value.set.as_ref(),
            value.func.as_ref(),
            verify_state,
        )
    }
    pub(super) fn verify_product_obj_well_definedness_by_def(
        &mut self,
        value: &Product,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_objs_as_children(
            &[
                value.start.as_ref(),
                value.end.as_ref(),
                value.func.as_ref(),
            ],
            verify_state,
        )
    }
    pub(super) fn verify_product_of_finite_set_obj_well_definedness_by_def(
        &mut self,
        value: &ProductOfFiniteSet,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_binary_obj_well_definedness_by_def(
            value.set.as_ref(),
            value.func.as_ref(),
            verify_state,
        )
    }
    pub(super) fn verify_reduce_obj_well_definedness_by_def(
        &mut self,
        value: &Reduce,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_objs_as_children(
            &[
                value.start.as_ref(),
                value.end.as_ref(),
                value.func.as_ref(),
                value.op.as_ref(),
                value.seed.as_ref(),
            ],
            verify_state,
        )
    }
    pub(super) fn verify_finite_set_reduce_obj_well_definedness_by_def(
        &mut self,
        value: &FiniteSetReduce,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_objs_as_children(
            &[
                value.set.as_ref(),
                value.func.as_ref(),
                value.op.as_ref(),
                value.seed.as_ref(),
            ],
            verify_state,
        )
    }
    pub(super) fn verify_range_obj_well_definedness_by_def(
        &mut self,
        value: &Range,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_binary_obj_well_definedness_by_def(
            value.start.as_ref(),
            value.end.as_ref(),
            verify_state,
        )
    }
    pub(super) fn verify_closed_range_obj_well_definedness_by_def(
        &mut self,
        value: &ClosedRange,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_binary_obj_well_definedness_by_def(
            value.start.as_ref(),
            value.end.as_ref(),
            verify_state,
        )
    }
    pub(super) fn verify_finite_seq_set_obj_well_definedness_by_def(
        &mut self,
        value: &FiniteSeqSet,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_binary_obj_well_definedness_by_def(
            value.set.as_ref(),
            value.n.as_ref(),
            verify_state,
        )
    }
    pub(super) fn verify_seq_set_obj_well_definedness_by_def(
        &mut self,
        value: &SeqSet,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_unary_obj_well_definedness_by_def(value.set.as_ref(), verify_state)
    }
    pub(super) fn verify_finite_seq_list_obj_well_definedness_by_def(
        &mut self,
        value: &FiniteSeqListObj,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_boxed_objs_as_children(&value.objs, verify_state)
    }
    pub(super) fn verify_obj_at_index_obj_well_definedness_by_def(
        &mut self,
        value: &ObjAtIndex,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_binary_obj_well_definedness_by_def(
            value.obj.as_ref(),
            value.index.as_ref(),
            verify_state,
        )
    }
}
