//! Iterated / range / sequence object WD.
//! ObjAtIndex + Range/ClosedRange (endpoints in Z) + FiniteSeqSet/SeqSet light
//! `$is_set` / length-in-N. Sum/Product/Reduce stay children-only (Option 1 defer).

use super::obj_well_defined_by_def_common::ObjWellDefinedByDefCommonStages;
use crate::new_pipeline::ast::fact::{AtomicFact, IsTupleFact, LessEqualFact};
use crate::new_pipeline::ast::obj::{
    ClosedRange, FiniteSeqSet, FiniteSetReduce, Obj, ObjAtIndex, Product,
    ProductOfFiniteSet, Range, Reduce, SeqSet, StandardSet, Sum, SumOfFiniteSet, TupleDim,
};
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

impl Runtime {
    pub(super) fn verify_sum_obj_well_definedness_by_def(
        &mut self,
        value: &Sum,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
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
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
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
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
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
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
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
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
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
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
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
    // range(start, end): children, then both endpoints $in Z.
    // Example: `range(1, 3)`.
    pub(super) fn verify_range_obj_well_definedness_by_def(
        &mut self,
        value: &Range,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        let proof = self.verify_binary_obj_well_definedness_by_def(
            value.start.as_ref(),
            value.end.as_ref(),
            verify_state.clone(),
        )?;
        let mut reqs = Vec::new();
        reqs.push(self.require_obj_in_standard_set(
            value.start.as_ref(),
            StandardSet::Z,
            verify_state.clone(),
            format!("range start {} is not in Z", value.start.ir()),
        )?);
        reqs.push(self.require_obj_in_standard_set(
            value.end.as_ref(),
            StandardSet::Z,
            verify_state,
            format!("range end {} is not in Z", value.end.ir()),
        )?);
        Ok(self.with_requirements(proof, reqs))
    }

    // closed_range(start, end): same Z carrier obligations as range.
    pub(super) fn verify_closed_range_obj_well_definedness_by_def(
        &mut self,
        value: &ClosedRange,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        let proof = self.verify_binary_obj_well_definedness_by_def(
            value.start.as_ref(),
            value.end.as_ref(),
            verify_state.clone(),
        )?;
        let mut reqs = Vec::new();
        reqs.push(self.require_obj_in_standard_set(
            value.start.as_ref(),
            StandardSet::Z,
            verify_state.clone(),
            format!("closed_range start {} is not in Z", value.start.ir()),
        )?);
        reqs.push(self.require_obj_in_standard_set(
            value.end.as_ref(),
            StandardSet::Z,
            verify_state,
            format!("closed_range end {} is not in Z", value.end.ir()),
        )?);
        Ok(self.with_requirements(proof, reqs))
    }

    // finite_seq_set(S, n): children, `$is_set(S)`, `n $in N`.
    pub(super) fn verify_finite_seq_set_obj_well_definedness_by_def(
        &mut self,
        value: &FiniteSeqSet,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        let proof = self.verify_binary_obj_well_definedness_by_def(
            value.set.as_ref(),
            value.n.as_ref(),
            verify_state.clone(),
        )?;
        let mut reqs = Vec::new();
        reqs.push(self.require_is_set(
            value.set.as_ref(),
            verify_state.clone(),
            format!(
                "finite_seq_set: first argument {} is not a set",
                value.set.ir()
            ),
        )?);
        reqs.push(self.require_obj_in_standard_set(
            value.n.as_ref(),
            StandardSet::N,
            verify_state,
            format!(
                "finite_seq_set: length {} is not verified in N",
                value.n.ir()
            ),
        )?);
        Ok(self.with_requirements(proof, reqs))
    }

    // seq_set(S): children, `$is_set(S)`.
    pub(super) fn verify_seq_set_obj_well_definedness_by_def(
        &mut self,
        value: &SeqSet,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        let proof = self
            .verify_unary_obj_well_definedness_by_def(value.set.as_ref(), verify_state.clone())?;
        let req = self.require_is_set(
            value.set.as_ref(),
            verify_state,
            format!("seq_set: argument {} is not a set", value.set.ir()),
        )?;
        Ok(self.with_requirements(proof, vec![req]))
    }
    // t[i]: children, then `i $in N+`, `$is_tuple(t)`, `i <= tuple_dim(t)`.
    // Example: `(1, 2)[1]` is WD; `(1, 2)[0]` fails `0 $in N+`; `(1, 2)[3]` fails bound.
    pub(super) fn verify_obj_at_index_obj_well_definedness_by_def(
        &mut self,
        value: &ObjAtIndex,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        let proof = self.verify_binary_obj_well_definedness_by_def(
            value.obj.as_ref(),
            value.index.as_ref(),
            verify_state.clone(),
        )?;
        let mut reqs = Vec::new();
        reqs.push(self.require_obj_in_standard_set(
            value.index.as_ref(),
            StandardSet::NPos,
            verify_state.clone(),
            format!("index {} is not a positive integer", value.index.ir()),
        )?);
        let is_tuple = AtomicFact::IsTupleFact(IsTupleFact {
            fact_id: self.ids.allocate_fact_id(),
            set: value.obj.as_ref().clone(),
            line_file: None,
        });
        reqs.push(self.verify_required_atomic_fact(
            is_tuple,
            verify_state.clone(),
            format!("index target {} is not a tuple", value.obj.ir()),
        )?);
        let tuple_dim: Obj = Obj::TupleDim(TupleDim {
            arg: value.obj.clone(),
        });
        let bounded = AtomicFact::LessEqualFact(LessEqualFact {
            fact_id: self.ids.allocate_fact_id(),
            left: value.index.as_ref().clone(),
            right: tuple_dim.clone(),
            line_file: None,
        });
        reqs.push(self.verify_required_atomic_fact(
            bounded,
            verify_state,
            format!("{} <= {} is unknown", value.index.ir(), tuple_dim.ir()),
        )?);
        Ok(self.with_requirements(proof, reqs))
    }
}
