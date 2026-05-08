use crate::prelude::*;
use crate::verify::verify_equality_by_builtin_rules::{
    factual_equal_success_by_builtin_reason, verify_equality_by_they_are_the_same,
};
use std::rc::Rc;

impl Runtime {
    fn try_verify_equality_pair_by_the_same_then_calculation_then_fn_obj_same_head_known_args(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let (result, _, _) = self.verify_equality_by_they_are_the_same_and_calculation(
            left,
            right,
            line_file.clone(),
            verify_state,
        )?;
        if result.is_true() {
            return Ok(Some(result));
        }
        if let Some(shape_result) =
            self.try_verify_equal_by_same_shape_and_known_equality_args(left, right, line_file)
        {
            if shape_result.is_true() {
                return Ok(Some(shape_result));
            }
        }
        Ok(None)
    }

    pub fn try_verify_equality_with_known_equalities_by_builtin_rules_only(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
        known_objs_equal_to_left: Option<&Rc<Vec<Obj>>>,
        known_objs_equal_to_right: Option<&Rc<Vec<Obj>>>,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        match (known_objs_equal_to_left, known_objs_equal_to_right) {
            (None, None) => Ok(None),
            (Some(known_objs_equal_to_left), None) => {
                for obj in known_objs_equal_to_left.iter() {
                    if let Some(result) = self
                        .try_verify_equality_pair_by_the_same_then_calculation_then_fn_obj_same_head_known_args(
                            obj,
                            right,
                            line_file.clone(),
                            verify_state,
                        )?
                    {
                        return Ok(Some(result));
                    }
                }
                Ok(None)
            }
            (None, Some(known_objs_equal_to_right)) => {
                for obj in known_objs_equal_to_right.iter() {
                    if let Some(result) = self
                        .try_verify_equality_pair_by_the_same_then_calculation_then_fn_obj_same_head_known_args(
                            left,
                            obj,
                            line_file.clone(),
                            verify_state,
                        )?
                    {
                        return Ok(Some(result));
                    }
                }
                Ok(None)
            }
            (Some(known_objs_equal_to_left), Some(known_objs_equal_to_right)) => {
                for obj1 in known_objs_equal_to_left.iter() {
                    for obj2 in known_objs_equal_to_right.iter() {
                        if let Some(result) = self
                            .try_verify_equality_pair_by_the_same_then_calculation_then_fn_obj_same_head_known_args(
                                obj1,
                                obj2,
                                line_file.clone(),
                                verify_state,
                            )?
                        {
                            return Ok(Some(result));
                        }
                    }
                }
                Ok(None)
            }
        }
    }

    pub fn objs_have_same_known_equality_rc_in_some_env(&self, left: &Obj, right: &Obj) -> bool {
        let left_key: ObjString = left.to_string();
        let right_key: ObjString = right.to_string();
        for env in self.iter_environments_from_top() {
            let left_entry = env.known_equality.get(&left_key);
            let right_entry = env.known_equality.get(&right_key);
            if let (Some((_, left_rc)), Some((_, right_rc))) = (left_entry, right_entry) {
                if Rc::ptr_eq(left_rc, right_rc) {
                    return true;
                }
            }
        }
        false
    }

    fn arg_pairs_share_known_equality_class(&self, pairs: &[(&Obj, &Obj)]) -> bool {
        pairs
            .iter()
            .all(|(a, b)| self.objs_have_same_known_equality_rc_in_some_env(a, b))
    }

    fn boxed_obj_vecs_share_known_equality_class(
        &self,
        left: &[Box<Obj>],
        right: &[Box<Obj>],
    ) -> bool {
        if left.len() != right.len() {
            return false;
        }
        left.iter()
            .zip(right.iter())
            .all(|(a, b)| self.objs_have_same_known_equality_rc_in_some_env(a, b))
    }

    pub fn try_verify_equal_by_same_shape_and_known_equality_args(
        &self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
    ) -> Option<StmtResult> {
        let reason = "same shape and paired args share known equality class";
        match (left, right) {
            (Obj::FnObj(left_fn), Obj::FnObj(right_fn)) => {
                let left_head_obj = left_fn.head.as_ref().clone().into();
                let right_head_obj = right_fn.head.as_ref().clone().into();
                if !verify_equality_by_they_are_the_same(&left_head_obj, &right_head_obj) {
                    return Some((StmtUnknown::new()).into());
                }
                if left_fn.body.len() != right_fn.body.len() {
                    return Some((StmtUnknown::new()).into());
                }
                for (left_group, right_group) in left_fn.body.iter().zip(right_fn.body.iter()) {
                    if !self.boxed_obj_vecs_share_known_equality_class(left_group, right_group) {
                        return Some((StmtUnknown::new()).into());
                    }
                }
                Some(factual_equal_success_by_builtin_reason(
                    left, right, line_file, reason,
                ))
            }
            (Obj::Add(l), Obj::Add(r)) => {
                if self.arg_pairs_share_known_equality_class(&[
                    (&l.left, &r.left),
                    (&l.right, &r.right),
                ]) {
                    Some(factual_equal_success_by_builtin_reason(
                        left, right, line_file, reason,
                    ))
                } else {
                    Some((StmtUnknown::new()).into())
                }
            }
            (Obj::MatrixAdd(l), Obj::MatrixAdd(r)) => {
                if self.arg_pairs_share_known_equality_class(&[
                    (&l.left, &r.left),
                    (&l.right, &r.right),
                ]) {
                    Some(factual_equal_success_by_builtin_reason(
                        left, right, line_file, reason,
                    ))
                } else {
                    Some((StmtUnknown::new()).into())
                }
            }
            (Obj::MatrixSub(l), Obj::MatrixSub(r)) => {
                if self.arg_pairs_share_known_equality_class(&[
                    (&l.left, &r.left),
                    (&l.right, &r.right),
                ]) {
                    Some(factual_equal_success_by_builtin_reason(
                        left, right, line_file, reason,
                    ))
                } else {
                    Some((StmtUnknown::new()).into())
                }
            }
            (Obj::MatrixMul(l), Obj::MatrixMul(r)) => {
                if self.arg_pairs_share_known_equality_class(&[
                    (&l.left, &r.left),
                    (&l.right, &r.right),
                ]) {
                    Some(factual_equal_success_by_builtin_reason(
                        left, right, line_file, reason,
                    ))
                } else {
                    Some((StmtUnknown::new()).into())
                }
            }
            (Obj::MatrixScalarMul(l), Obj::MatrixScalarMul(r)) => {
                if self.arg_pairs_share_known_equality_class(&[
                    (&l.scalar, &r.scalar),
                    (&l.matrix, &r.matrix),
                ]) {
                    Some(factual_equal_success_by_builtin_reason(
                        left, right, line_file, reason,
                    ))
                } else {
                    Some((StmtUnknown::new()).into())
                }
            }
            (Obj::MatrixPow(l), Obj::MatrixPow(r)) => {
                if self.arg_pairs_share_known_equality_class(&[
                    (&l.base, &r.base),
                    (&l.exponent, &r.exponent),
                ]) {
                    Some(factual_equal_success_by_builtin_reason(
                        left, right, line_file, reason,
                    ))
                } else {
                    Some((StmtUnknown::new()).into())
                }
            }
            (Obj::Sub(l), Obj::Sub(r)) => {
                if self.arg_pairs_share_known_equality_class(&[
                    (&l.left, &r.left),
                    (&l.right, &r.right),
                ]) {
                    Some(factual_equal_success_by_builtin_reason(
                        left, right, line_file, reason,
                    ))
                } else {
                    Some((StmtUnknown::new()).into())
                }
            }
            (Obj::Mul(l), Obj::Mul(r)) => {
                if self.arg_pairs_share_known_equality_class(&[
                    (&l.left, &r.left),
                    (&l.right, &r.right),
                ]) {
                    Some(factual_equal_success_by_builtin_reason(
                        left, right, line_file, reason,
                    ))
                } else {
                    Some((StmtUnknown::new()).into())
                }
            }
            (Obj::Div(l), Obj::Div(r)) => {
                if self.arg_pairs_share_known_equality_class(&[
                    (&l.left, &r.left),
                    (&l.right, &r.right),
                ]) {
                    Some(factual_equal_success_by_builtin_reason(
                        left, right, line_file, reason,
                    ))
                } else {
                    Some((StmtUnknown::new()).into())
                }
            }
            (Obj::Mod(l), Obj::Mod(r)) => {
                if self.arg_pairs_share_known_equality_class(&[
                    (&l.left, &r.left),
                    (&l.right, &r.right),
                ]) {
                    Some(factual_equal_success_by_builtin_reason(
                        left, right, line_file, reason,
                    ))
                } else {
                    Some((StmtUnknown::new()).into())
                }
            }
            (Obj::Pow(l), Obj::Pow(r)) => {
                if self.arg_pairs_share_known_equality_class(&[
                    (&l.base, &r.base),
                    (&l.exponent, &r.exponent),
                ]) {
                    Some(factual_equal_success_by_builtin_reason(
                        left, right, line_file, reason,
                    ))
                } else {
                    Some((StmtUnknown::new()).into())
                }
            }
            (Obj::Log(l), Obj::Log(r)) => {
                if self
                    .arg_pairs_share_known_equality_class(&[(&l.base, &r.base), (&l.arg, &r.arg)])
                {
                    Some(factual_equal_success_by_builtin_reason(
                        left, right, line_file, reason,
                    ))
                } else {
                    Some((StmtUnknown::new()).into())
                }
            }
            (Obj::Max(l), Obj::Max(r)) => {
                if self.arg_pairs_share_known_equality_class(&[
                    (&l.left, &r.left),
                    (&l.right, &r.right),
                ]) {
                    Some(factual_equal_success_by_builtin_reason(
                        left, right, line_file, reason,
                    ))
                } else {
                    Some((StmtUnknown::new()).into())
                }
            }
            (Obj::Min(l), Obj::Min(r)) => {
                if self.arg_pairs_share_known_equality_class(&[
                    (&l.left, &r.left),
                    (&l.right, &r.right),
                ]) {
                    Some(factual_equal_success_by_builtin_reason(
                        left, right, line_file, reason,
                    ))
                } else {
                    Some((StmtUnknown::new()).into())
                }
            }
            (Obj::Union(l), Obj::Union(r)) => {
                if self.arg_pairs_share_known_equality_class(&[
                    (&l.left, &r.left),
                    (&l.right, &r.right),
                ]) {
                    Some(factual_equal_success_by_builtin_reason(
                        left, right, line_file, reason,
                    ))
                } else {
                    Some((StmtUnknown::new()).into())
                }
            }
            (Obj::Intersect(l), Obj::Intersect(r)) => {
                if self.arg_pairs_share_known_equality_class(&[
                    (&l.left, &r.left),
                    (&l.right, &r.right),
                ]) {
                    Some(factual_equal_success_by_builtin_reason(
                        left, right, line_file, reason,
                    ))
                } else {
                    Some((StmtUnknown::new()).into())
                }
            }
            (Obj::SetMinus(l), Obj::SetMinus(r)) => {
                if self.arg_pairs_share_known_equality_class(&[
                    (&l.left, &r.left),
                    (&l.right, &r.right),
                ]) {
                    Some(factual_equal_success_by_builtin_reason(
                        left, right, line_file, reason,
                    ))
                } else {
                    Some((StmtUnknown::new()).into())
                }
            }
            (Obj::SetDiff(l), Obj::SetDiff(r)) => {
                if self.arg_pairs_share_known_equality_class(&[
                    (&l.left, &r.left),
                    (&l.right, &r.right),
                ]) {
                    Some(factual_equal_success_by_builtin_reason(
                        left, right, line_file, reason,
                    ))
                } else {
                    Some((StmtUnknown::new()).into())
                }
            }
            (Obj::Cup(l), Obj::Cup(r)) => {
                if self.objs_have_same_known_equality_rc_in_some_env(&l.left, &r.left) {
                    Some(factual_equal_success_by_builtin_reason(
                        left, right, line_file, reason,
                    ))
                } else {
                    Some((StmtUnknown::new()).into())
                }
            }
            (Obj::Cap(l), Obj::Cap(r)) => {
                if self.objs_have_same_known_equality_rc_in_some_env(&l.left, &r.left) {
                    Some(factual_equal_success_by_builtin_reason(
                        left, right, line_file, reason,
                    ))
                } else {
                    Some((StmtUnknown::new()).into())
                }
            }
            (Obj::PowerSet(l), Obj::PowerSet(r)) => {
                if self.objs_have_same_known_equality_rc_in_some_env(&l.set, &r.set) {
                    Some(factual_equal_success_by_builtin_reason(
                        left, right, line_file, reason,
                    ))
                } else {
                    Some((StmtUnknown::new()).into())
                }
            }
            (Obj::Choose(l), Obj::Choose(r)) => {
                if self.objs_have_same_known_equality_rc_in_some_env(&l.set, &r.set) {
                    Some(factual_equal_success_by_builtin_reason(
                        left, right, line_file, reason,
                    ))
                } else {
                    Some((StmtUnknown::new()).into())
                }
            }
            (Obj::CartDim(l), Obj::CartDim(r)) => {
                if self.objs_have_same_known_equality_rc_in_some_env(&l.set, &r.set) {
                    Some(factual_equal_success_by_builtin_reason(
                        left, right, line_file, reason,
                    ))
                } else {
                    Some((StmtUnknown::new()).into())
                }
            }
            (Obj::TupleDim(l), Obj::TupleDim(r)) => {
                if self.objs_have_same_known_equality_rc_in_some_env(&l.arg, &r.arg) {
                    Some(factual_equal_success_by_builtin_reason(
                        left, right, line_file, reason,
                    ))
                } else {
                    Some((StmtUnknown::new()).into())
                }
            }
            (Obj::Count(l), Obj::Count(r)) => {
                if self.objs_have_same_known_equality_rc_in_some_env(&l.set, &r.set) {
                    Some(factual_equal_success_by_builtin_reason(
                        left, right, line_file, reason,
                    ))
                } else {
                    Some((StmtUnknown::new()).into())
                }
            }
            (Obj::Range(l), Obj::Range(r)) => {
                if self
                    .arg_pairs_share_known_equality_class(&[(&l.start, &r.start), (&l.end, &r.end)])
                {
                    Some(factual_equal_success_by_builtin_reason(
                        left, right, line_file, reason,
                    ))
                } else {
                    Some((StmtUnknown::new()).into())
                }
            }
            (Obj::Sum(l), Obj::Sum(r)) => {
                if self.arg_pairs_share_known_equality_class(&[
                    (&l.start, &r.start),
                    (&l.end, &r.end),
                    (&l.func, &r.func),
                ]) {
                    Some(factual_equal_success_by_builtin_reason(
                        left, right, line_file, reason,
                    ))
                } else {
                    Some((StmtUnknown::new()).into())
                }
            }
            (Obj::Product(l), Obj::Product(r)) => {
                if self.arg_pairs_share_known_equality_class(&[
                    (&l.start, &r.start),
                    (&l.end, &r.end),
                    (&l.func, &r.func),
                ]) {
                    Some(factual_equal_success_by_builtin_reason(
                        left, right, line_file, reason,
                    ))
                } else {
                    Some((StmtUnknown::new()).into())
                }
            }
            (Obj::ClosedRange(l), Obj::ClosedRange(r)) => {
                if self
                    .arg_pairs_share_known_equality_class(&[(&l.start, &r.start), (&l.end, &r.end)])
                {
                    Some(factual_equal_success_by_builtin_reason(
                        left, right, line_file, reason,
                    ))
                } else {
                    Some((StmtUnknown::new()).into())
                }
            }
            (Obj::FiniteSeqSet(l), Obj::FiniteSeqSet(r)) => {
                if self.arg_pairs_share_known_equality_class(&[(&l.set, &r.set), (&l.n, &r.n)]) {
                    Some(factual_equal_success_by_builtin_reason(
                        left, right, line_file, reason,
                    ))
                } else {
                    Some((StmtUnknown::new()).into())
                }
            }
            (Obj::SeqSet(l), Obj::SeqSet(r)) => {
                if self.arg_pairs_share_known_equality_class(&[(&l.set, &r.set)]) {
                    Some(factual_equal_success_by_builtin_reason(
                        left, right, line_file, reason,
                    ))
                } else {
                    Some((StmtUnknown::new()).into())
                }
            }
            (Obj::MatrixSet(l), Obj::MatrixSet(r)) => {
                if self.arg_pairs_share_known_equality_class(&[
                    (&l.set, &r.set),
                    (&l.row_len, &r.row_len),
                    (&l.col_len, &r.col_len),
                ]) {
                    Some(factual_equal_success_by_builtin_reason(
                        left, right, line_file, reason,
                    ))
                } else {
                    Some((StmtUnknown::new()).into())
                }
            }
            (Obj::Proj(l), Obj::Proj(r)) => {
                if self.arg_pairs_share_known_equality_class(&[(&l.set, &r.set), (&l.dim, &r.dim)])
                {
                    Some(factual_equal_success_by_builtin_reason(
                        left, right, line_file, reason,
                    ))
                } else {
                    Some((StmtUnknown::new()).into())
                }
            }
            (Obj::ObjAtIndex(l), Obj::ObjAtIndex(r)) => {
                if self
                    .arg_pairs_share_known_equality_class(&[(&l.obj, &r.obj), (&l.index, &r.index)])
                {
                    Some(factual_equal_success_by_builtin_reason(
                        left, right, line_file, reason,
                    ))
                } else {
                    Some((StmtUnknown::new()).into())
                }
            }
            (Obj::Tuple(l), Obj::Tuple(r)) => {
                if self.boxed_obj_vecs_share_known_equality_class(&l.args, &r.args) {
                    Some(factual_equal_success_by_builtin_reason(
                        left, right, line_file, reason,
                    ))
                } else {
                    Some((StmtUnknown::new()).into())
                }
            }
            (Obj::ListSet(l), Obj::ListSet(r)) => {
                if self.boxed_obj_vecs_share_known_equality_class(&l.list, &r.list) {
                    Some(factual_equal_success_by_builtin_reason(
                        left, right, line_file, reason,
                    ))
                } else {
                    Some((StmtUnknown::new()).into())
                }
            }
            (Obj::Cart(l), Obj::Cart(r)) => {
                if self.boxed_obj_vecs_share_known_equality_class(&l.args, &r.args) {
                    Some(factual_equal_success_by_builtin_reason(
                        left, right, line_file, reason,
                    ))
                } else {
                    Some((StmtUnknown::new()).into())
                }
            }
            _ => None,
        }
    }

    pub fn verify_equality_by_they_are_the_same_and_calculation(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        _verify_state: &VerifyState,
    ) -> Result<(StmtResult, Obj, Obj), RuntimeError> {
        if verify_equality_by_they_are_the_same(left, right) {
            return Ok((
                factual_equal_success_by_builtin_reason(
                    left,
                    right,
                    line_file,
                    "they are the same",
                ),
                left.clone(),
                right.clone(),
            ));
        }

        let left_resolved = self.resolve_obj(left);
        let right_resolved = self.resolve_obj(right);

        if left_resolved.two_objs_can_be_calculated_and_equal_by_calculation(&right_resolved) {
            return Ok((
                factual_equal_success_by_builtin_reason(left, right, line_file, "calculation"),
                left_resolved,
                right_resolved,
            ));
        }

        Ok((
            StmtResult::StmtUnknown(StmtUnknown::new()),
            left_resolved,
            right_resolved,
        ))
    }
}
