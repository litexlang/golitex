use crate::prelude::*;
use std::rc::Rc;

pub fn verify_equality_by_they_are_the_same(left: &Obj, right: &Obj) -> bool {
    if left.to_string() == right.to_string() {
        return true;
    }
    false
}

fn factual_equal_success_by_builtin_reason(
    left: &Obj,
    right: &Obj,
    line_file: LineFile,
    reason: &str,
) -> StmtExecResult {
    StmtExecResult::FactualStmtSuccess(
        FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
            Fact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(
                left.clone(),
                right.clone(),
                line_file,
            ))),
            reason.to_string(),
            Vec::new(),
        ),
    )
}

impl Runtime {
    // Instantiate family `equal_to` on one or both sides, then full `verify_objs_are_equal` on the expanded pair.
    fn try_verify_objs_equal_by_expanding_family(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtExecResult>, RuntimeError> {
        if let (Obj::FamilyObj(fl), Obj::FamilyObj(fr)) = (left, right) {
            if let (Ok(el), Ok(er)) = (
                self.instantiate_family_member_set(fl),
                self.instantiate_family_member_set(fr),
            ) {
                let r = self.verify_objs_are_equal(&el, &er, line_file.clone(), verify_state)?;
                if r.is_true() {
                    return Ok(Some(factual_equal_success_by_builtin_reason(
                        left,
                        right,
                        line_file,
                        "equality: expand family definition (substitute parameters into equal_to)",
                    )));
                }
            }
        }
        if let Obj::FamilyObj(f) = left {
            if let Ok(expanded) = self.instantiate_family_member_set(f) {
                let r =
                    self.verify_objs_are_equal(&expanded, right, line_file.clone(), verify_state)?;
                if r.is_true() {
                    return Ok(Some(factual_equal_success_by_builtin_reason(
                        left,
                        right,
                        line_file,
                        "equality: expand family definition (substitute parameters into equal_to)",
                    )));
                }
            }
        }
        if let Obj::FamilyObj(f) = right {
            if let Ok(expanded) = self.instantiate_family_member_set(f) {
                let r =
                    self.verify_objs_are_equal(left, &expanded, line_file.clone(), verify_state)?;
                if r.is_true() {
                    return Ok(Some(factual_equal_success_by_builtin_reason(
                        left,
                        right,
                        line_file,
                        "equality: expand family definition (substitute parameters into equal_to)",
                    )));
                }
            }
        }
        Ok(None)
    }

    pub(crate) fn verify_equality_by_builtin_rules(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<StmtExecResult, RuntimeError> {
        if let Some(done) = self.try_verify_objs_equal_by_expanding_family(
            left,
            right,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(done);
        }

        let (result, calculated_left, calculated_right) = self
            .verify_equality_by_they_are_the_same_and_calculation(
                left,
                right,
                line_file.clone(),
                verify_state,
            )?;
        if result.is_true() {
            return Ok(result);
        }

        if objs_equal_by_rational_expression_evaluation(&calculated_left, &calculated_right) {
            return Ok(StmtExecResult::FactualStmtSuccess(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    Fact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(
                        left.clone(),
                        right.clone(),
                        line_file,
                    ))),
                    "calculation and rational expression simplification".to_string(),
                    Vec::new(),
                ),
            ));
        }

        if let (Obj::FnSet(left_fn_set), Obj::FnSet(right_fn_set)) = (left, right) {
            return self.verify_fn_set_with_params_equality_by_builtin_rules(
                left_fn_set,
                right_fn_set,
                line_file,
                verify_state,
            );
        }

        Ok(StmtExecResult::StmtUnknown(StmtUnknown::new()))
    }
}

impl Runtime {
    fn try_verify_equality_pair_by_the_same_then_calculation_then_fn_obj_same_head_known_args(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtExecResult>, RuntimeError> {
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

    pub(crate) fn try_verify_equality_with_known_equalities_by_builtin_rules_only(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
        known_objs_equal_to_left: Option<&Rc<Vec<Obj>>>,
        known_objs_equal_to_right: Option<&Rc<Vec<Obj>>>,
    ) -> Result<Option<StmtExecResult>, RuntimeError> {
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

    pub(crate) fn objs_have_same_known_equality_rc_in_some_env(
        &self,
        left: &Obj,
        right: &Obj,
    ) -> bool {
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

    pub(crate) fn try_verify_equal_by_same_shape_and_known_equality_args(
        &self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
    ) -> Option<StmtExecResult> {
        let reason = "same shape and paired args share known equality class";
        match (left, right) {
            (Obj::FnObj(left_fn), Obj::FnObj(right_fn)) => {
                let left_head_obj = Obj::from(left_fn.head.as_ref().clone());
                let right_head_obj = Obj::from(right_fn.head.as_ref().clone());
                if !verify_equality_by_they_are_the_same(&left_head_obj, &right_head_obj) {
                    return Some(StmtExecResult::StmtUnknown(StmtUnknown::new()));
                }
                if left_fn.body.len() != right_fn.body.len() {
                    return Some(StmtExecResult::StmtUnknown(StmtUnknown::new()));
                }
                for (left_group, right_group) in left_fn.body.iter().zip(right_fn.body.iter()) {
                    if !self.boxed_obj_vecs_share_known_equality_class(left_group, right_group) {
                        return Some(StmtExecResult::StmtUnknown(StmtUnknown::new()));
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
                    Some(StmtExecResult::StmtUnknown(StmtUnknown::new()))
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
                    Some(StmtExecResult::StmtUnknown(StmtUnknown::new()))
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
                    Some(StmtExecResult::StmtUnknown(StmtUnknown::new()))
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
                    Some(StmtExecResult::StmtUnknown(StmtUnknown::new()))
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
                    Some(StmtExecResult::StmtUnknown(StmtUnknown::new()))
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
                    Some(StmtExecResult::StmtUnknown(StmtUnknown::new()))
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
                    Some(StmtExecResult::StmtUnknown(StmtUnknown::new()))
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
                    Some(StmtExecResult::StmtUnknown(StmtUnknown::new()))
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
                    Some(StmtExecResult::StmtUnknown(StmtUnknown::new()))
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
                    Some(StmtExecResult::StmtUnknown(StmtUnknown::new()))
                }
            }
            (Obj::Cup(l), Obj::Cup(r)) => {
                if self.objs_have_same_known_equality_rc_in_some_env(&l.left, &r.left) {
                    Some(factual_equal_success_by_builtin_reason(
                        left, right, line_file, reason,
                    ))
                } else {
                    Some(StmtExecResult::StmtUnknown(StmtUnknown::new()))
                }
            }
            (Obj::Cap(l), Obj::Cap(r)) => {
                if self.objs_have_same_known_equality_rc_in_some_env(&l.left, &r.left) {
                    Some(factual_equal_success_by_builtin_reason(
                        left, right, line_file, reason,
                    ))
                } else {
                    Some(StmtExecResult::StmtUnknown(StmtUnknown::new()))
                }
            }
            (Obj::PowerSet(l), Obj::PowerSet(r)) => {
                if self.objs_have_same_known_equality_rc_in_some_env(&l.set, &r.set) {
                    Some(factual_equal_success_by_builtin_reason(
                        left, right, line_file, reason,
                    ))
                } else {
                    Some(StmtExecResult::StmtUnknown(StmtUnknown::new()))
                }
            }
            (Obj::Choose(l), Obj::Choose(r)) => {
                if self.objs_have_same_known_equality_rc_in_some_env(&l.set, &r.set) {
                    Some(factual_equal_success_by_builtin_reason(
                        left, right, line_file, reason,
                    ))
                } else {
                    Some(StmtExecResult::StmtUnknown(StmtUnknown::new()))
                }
            }
            (Obj::CartDim(l), Obj::CartDim(r)) => {
                if self.objs_have_same_known_equality_rc_in_some_env(&l.set, &r.set) {
                    Some(factual_equal_success_by_builtin_reason(
                        left, right, line_file, reason,
                    ))
                } else {
                    Some(StmtExecResult::StmtUnknown(StmtUnknown::new()))
                }
            }
            (Obj::TupleDim(l), Obj::TupleDim(r)) => {
                if self.objs_have_same_known_equality_rc_in_some_env(&l.arg, &r.arg) {
                    Some(factual_equal_success_by_builtin_reason(
                        left, right, line_file, reason,
                    ))
                } else {
                    Some(StmtExecResult::StmtUnknown(StmtUnknown::new()))
                }
            }
            (Obj::Count(l), Obj::Count(r)) => {
                if self.objs_have_same_known_equality_rc_in_some_env(&l.set, &r.set) {
                    Some(factual_equal_success_by_builtin_reason(
                        left, right, line_file, reason,
                    ))
                } else {
                    Some(StmtExecResult::StmtUnknown(StmtUnknown::new()))
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
                    Some(StmtExecResult::StmtUnknown(StmtUnknown::new()))
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
                    Some(StmtExecResult::StmtUnknown(StmtUnknown::new()))
                }
            }
            (Obj::Proj(l), Obj::Proj(r)) => {
                if self.arg_pairs_share_known_equality_class(&[(&l.set, &r.set), (&l.dim, &r.dim)])
                {
                    Some(factual_equal_success_by_builtin_reason(
                        left, right, line_file, reason,
                    ))
                } else {
                    Some(StmtExecResult::StmtUnknown(StmtUnknown::new()))
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
                    Some(StmtExecResult::StmtUnknown(StmtUnknown::new()))
                }
            }
            (Obj::Tuple(l), Obj::Tuple(r)) => {
                if self.boxed_obj_vecs_share_known_equality_class(&l.args, &r.args) {
                    Some(factual_equal_success_by_builtin_reason(
                        left, right, line_file, reason,
                    ))
                } else {
                    Some(StmtExecResult::StmtUnknown(StmtUnknown::new()))
                }
            }
            (Obj::ListSet(l), Obj::ListSet(r)) => {
                if self.boxed_obj_vecs_share_known_equality_class(&l.list, &r.list) {
                    Some(factual_equal_success_by_builtin_reason(
                        left, right, line_file, reason,
                    ))
                } else {
                    Some(StmtExecResult::StmtUnknown(StmtUnknown::new()))
                }
            }
            (Obj::Cart(l), Obj::Cart(r)) => {
                if self.boxed_obj_vecs_share_known_equality_class(&l.args, &r.args) {
                    Some(factual_equal_success_by_builtin_reason(
                        left, right, line_file, reason,
                    ))
                } else {
                    Some(StmtExecResult::StmtUnknown(StmtUnknown::new()))
                }
            }
            _ => None,
        }
    }

    pub(crate) fn verify_equality_by_they_are_the_same_and_calculation(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        _verify_state: &VerifyState,
    ) -> Result<(StmtExecResult, Obj, Obj), RuntimeError> {
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
            StmtExecResult::StmtUnknown(StmtUnknown::new()),
            left_resolved,
            right_resolved,
        ))
    }
}
