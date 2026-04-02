use crate::prelude::*;
use std::rc::Rc;

pub fn verify_equality_by_they_are_the_same(left: &Obj, right: &Obj) -> bool {
    if left.to_string() == right.to_string() {
        return true;
    }
    false
}

impl Runtime {
    pub(crate) fn verify_equality_by_builtin_rules(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<NonErrStmtExecResult, RuntimeError> {
        if verify_equality_by_they_are_the_same(left, right) {
            return Ok(NonErrStmtExecResult::FactualStmtSuccess(
                FactualStmtSuccess::new_with_verified_by_builtin_rules(
                    Fact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(
                        left.clone(),
                        right.clone(),
                        line_file,
                    ))),
                    InferResult::new(),
                    "the same".to_string(),
                    Vec::new(),
                ),
            ));
        }

        let left_for_numeric_verification = self.resolve_obj(left);
        let right_for_numeric_verification = self.resolve_obj(right);

        if left_for_numeric_verification
            .two_objs_can_be_calculated_and_equal_by_calculation(&right_for_numeric_verification)
        {
            return Ok(NonErrStmtExecResult::FactualStmtSuccess(
                FactualStmtSuccess::new_with_verified_by_builtin_rules(
                    Fact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(
                        left.clone(),
                        right.clone(),
                        line_file,
                    ))),
                    InferResult::new(),
                    "calculation".to_string(),
                    Vec::new(),
                ),
            ));
        }

        if objs_equal_by_rational_expression_evaluation(
            &left_for_numeric_verification,
            &right_for_numeric_verification,
        ) {
            return Ok(NonErrStmtExecResult::FactualStmtSuccess(
                FactualStmtSuccess::new_with_verified_by_builtin_rules(
                    Fact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(
                        left.clone(),
                        right.clone(),
                        line_file,
                    ))),
                    InferResult::new(),
                    "calculation and rational expression simplification".to_string(),
                    Vec::new(),
                ),
            ));
        }

        if let (Obj::FnSetWithParams(left_fn_set), Obj::FnSetWithParams(right_fn_set)) =
            (left, right)
        {
            return self.verify_fn_set_with_params_equality_by_builtin_rules(
                left_fn_set,
                right_fn_set,
                line_file,
                verify_state,
            );
        }

        Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()))
    }
}

impl Runtime {
    pub(crate) fn try_verify_equality_with_known_equalities_by_builtin_rules_only(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
        known_objs_equal_to_left: Option<&Rc<Vec<Obj>>>,
        known_objs_equal_to_right: Option<&Rc<Vec<Obj>>>,
    ) -> Result<Option<NonErrStmtExecResult>, RuntimeError> {
        match (known_objs_equal_to_left, known_objs_equal_to_right) {
            (None, None) => Ok(None),
            (Some(known_objs_equal_to_left), None) => {
                for obj in known_objs_equal_to_left.iter() {
                    let result =
                        self.verify_equality_by_builtin_rules(obj, right, line_file.clone(), verify_state)?;
                    if result.is_true() {
                        return Ok(Some(result));
                    }
                }
                Ok(None)
            }
            (None, Some(known_objs_equal_to_right)) => {
                for obj in known_objs_equal_to_right.iter() {
                    let result =
                        self.verify_equality_by_builtin_rules(left, obj, line_file.clone(), verify_state)?;
                    if result.is_true() {
                        return Ok(Some(result));
                    }
                }
                Ok(None)
            }
            (Some(known_objs_equal_to_left), Some(known_objs_equal_to_right)) => {
                for obj1 in known_objs_equal_to_left.iter() {
                    for obj2 in known_objs_equal_to_right.iter() {
                        let result = self.verify_equality_by_builtin_rules(
                            obj1,
                            obj2,
                            line_file.clone(),
                            verify_state,
                        )?;
                        if result.is_true() {
                            return Ok(Some(result));
                        }
                    }
                }
                Ok(None)
            }
        }
    }
}
