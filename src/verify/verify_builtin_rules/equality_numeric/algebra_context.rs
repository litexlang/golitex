use super::*;

impl Runtime {
    pub(super) fn verify_context_arg_equality(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<bool, RuntimeError> {
        Ok(self
            .verify_objs_are_equal_in_equality_builtin(left, right, line_file, verify_state)?
            .is_true())
    }

    // If equal objects appear in the same algebraic context, the whole context is equal.
    // Example: from `x = y`, infer `x + 1 = y + 1`.
    pub(crate) fn try_verify_same_algebra_context_by_equal_args(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let args_equal = match (left, right) {
            (Obj::Add(l), Obj::Add(r)) => {
                self.verify_context_arg_equality(
                    l.left.as_ref(),
                    r.left.as_ref(),
                    line_file.clone(),
                    verify_state,
                )? && self.verify_context_arg_equality(
                    l.right.as_ref(),
                    r.right.as_ref(),
                    line_file.clone(),
                    verify_state,
                )?
            }
            (Obj::Sub(l), Obj::Sub(r)) => {
                self.verify_context_arg_equality(
                    l.left.as_ref(),
                    r.left.as_ref(),
                    line_file.clone(),
                    verify_state,
                )? && self.verify_context_arg_equality(
                    l.right.as_ref(),
                    r.right.as_ref(),
                    line_file.clone(),
                    verify_state,
                )?
            }
            (Obj::Mul(l), Obj::Mul(r)) => {
                self.verify_context_arg_equality(
                    l.left.as_ref(),
                    r.left.as_ref(),
                    line_file.clone(),
                    verify_state,
                )? && self.verify_context_arg_equality(
                    l.right.as_ref(),
                    r.right.as_ref(),
                    line_file.clone(),
                    verify_state,
                )?
            }
            (Obj::Div(l), Obj::Div(r)) => {
                self.verify_context_arg_equality(
                    l.left.as_ref(),
                    r.left.as_ref(),
                    line_file.clone(),
                    verify_state,
                )? && self.verify_context_arg_equality(
                    l.right.as_ref(),
                    r.right.as_ref(),
                    line_file.clone(),
                    verify_state,
                )?
            }
            (Obj::Mod(l), Obj::Mod(r)) => {
                self.verify_context_arg_equality(
                    l.left.as_ref(),
                    r.left.as_ref(),
                    line_file.clone(),
                    verify_state,
                )? && self.verify_context_arg_equality(
                    l.right.as_ref(),
                    r.right.as_ref(),
                    line_file.clone(),
                    verify_state,
                )?
            }
            (Obj::Pow(l), Obj::Pow(r)) => {
                self.verify_context_arg_equality(
                    l.base.as_ref(),
                    r.base.as_ref(),
                    line_file.clone(),
                    verify_state,
                )? && self.verify_context_arg_equality(
                    l.exponent.as_ref(),
                    r.exponent.as_ref(),
                    line_file.clone(),
                    verify_state,
                )?
            }
            _ => return Ok(None),
        };
        if !args_equal {
            return Ok(None);
        }
        Ok(Some(factual_equal_success_by_builtin_reason(
            left,
            right,
            line_file,
            "equality: same algebraic context with equal arguments",
        )))
    }
}
