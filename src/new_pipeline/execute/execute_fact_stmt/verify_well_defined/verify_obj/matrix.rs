//! Matrix / interval object WD (children only until P3).

use super::entry::ObjWellDefinedProofByDef;
use crate::new_pipeline::ast::obj::{
    IntervalObj, IntervalObjStruct, MatrixAdd, MatrixListObj, MatrixMul, MatrixPow,
    MatrixScalarMul, MatrixSet, MatrixSub, OneSideInfinityIntervalObj,
};
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

impl Runtime {
    pub(super) fn verify_matrix_set_obj_well_definedness_by_def(
        &mut self, value: &MatrixSet, verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_objs_as_children(&[value.set.as_ref(), value.row_len.as_ref(), value.col_len.as_ref()], verify_state)
    }
    pub(super) fn verify_matrix_list_obj_well_definedness_by_def(
        &mut self, value: &MatrixListObj, verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        let mut children = Vec::new();
        for row in &value.rows {
            for cell in row { children.push(cell.as_ref()); }
        }
        self.verify_objs_as_children(&children, verify_state)
    }
    pub(super) fn verify_matrix_add_obj_well_definedness_by_def(
        &mut self, value: &MatrixAdd, verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_binary_obj_well_definedness_by_def(value.left.as_ref(), value.right.as_ref(), verify_state)
    }
    pub(super) fn verify_matrix_sub_obj_well_definedness_by_def(
        &mut self, value: &MatrixSub, verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_binary_obj_well_definedness_by_def(value.left.as_ref(), value.right.as_ref(), verify_state)
    }
    pub(super) fn verify_matrix_mul_obj_well_definedness_by_def(
        &mut self, value: &MatrixMul, verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_binary_obj_well_definedness_by_def(value.left.as_ref(), value.right.as_ref(), verify_state)
    }
    pub(super) fn verify_matrix_scalar_mul_obj_well_definedness_by_def(
        &mut self, value: &MatrixScalarMul, verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_binary_obj_well_definedness_by_def(value.scalar.as_ref(), value.matrix.as_ref(), verify_state)
    }
    pub(super) fn verify_matrix_pow_obj_well_definedness_by_def(
        &mut self, value: &MatrixPow, verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        self.verify_binary_obj_well_definedness_by_def(value.base.as_ref(), value.exponent.as_ref(), verify_state)
    }
    pub(super) fn verify_one_side_infinity_interval_obj_well_definedness_by_def(
        &mut self, value: &OneSideInfinityIntervalObj, verify_state: VerifyState,
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
        &mut self, value: &IntervalObj, verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        let bounds: &IntervalObjStruct = match value {
            IntervalObj::LeftOpenRightOpen(v)
            | IntervalObj::LeftOpenRightClosed(v)
            | IntervalObj::LeftClosedRightOpen(v)
            | IntervalObj::LeftClosedRightClosed(v) => v,
        };
        self.verify_binary_obj_well_definedness_by_def(bounds.start.as_ref(), bounds.end.as_ref(), verify_state)
    }
}
