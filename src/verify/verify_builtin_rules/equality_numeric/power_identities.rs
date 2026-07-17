use super::*;

impl Runtime {
    // First power identity: `a^1 = a`.
    // Example: `forall a Z: a^1 = a`.
    pub(crate) fn try_verify_pow_one_identity(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let (pow, other) = match (left, right) {
            (Obj::Pow(p), other) => (p, other),
            (other, Obj::Pow(p)) => (p, other),
            _ => return Ok(None),
        };
        if !Self::obj_is_builtin_literal_one(pow.exponent.as_ref()) {
            return Ok(None);
        }
        if !self
            .verify_objs_are_equal_in_equality_builtin(
                pow.base.as_ref(),
                other,
                line_file.clone(),
                verify_state,
            )?
            .is_true()
        {
            return Ok(None);
        }
        Ok(Some(factual_equal_success_by_builtin_reason(
            left,
            right,
            line_file,
            "equality: a^1 = a",
        )))
    }

    // Zeroth power identity under the natural-exponent convention: `a^0 = 1`,
    // including `0^0 = 1`.
    // Example: `forall a R: a^0 = 1`.
    pub(crate) fn try_verify_pow_zero_identity(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let pow = if Self::obj_is_builtin_literal_one(left) {
            match right {
                Obj::Pow(p) => p,
                _ => return Ok(None),
            }
        } else if Self::obj_is_builtin_literal_one(right) {
            match left {
                Obj::Pow(p) => p,
                _ => return Ok(None),
            }
        } else {
            return Ok(None);
        };
        if !Self::obj_is_builtin_literal_zero(pow.exponent.as_ref()) {
            return Ok(None);
        }
        Ok(Some(factual_equal_success_by_builtin_reason(
            left,
            right,
            line_file,
            "equality: a^0 = 1",
        )))
    }

    // One as a base is invariant under exponentiation: `1^x = 1`.
    // This is used for simplifying powers with arbitrary well-defined exponents.
    // Example: `forall x R: 1^x = 1`.
    pub(crate) fn try_verify_one_pow_identity(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let pow = if Self::obj_is_builtin_literal_one(left) {
            match right {
                Obj::Pow(p) => p,
                _ => return Ok(None),
            }
        } else if Self::obj_is_builtin_literal_one(right) {
            match left {
                Obj::Pow(p) => p,
                _ => return Ok(None),
            }
        } else {
            return Ok(None);
        };
        if !Self::obj_is_builtin_literal_one(pow.base.as_ref()) {
            return Ok(None);
        }
        Ok(Some(factual_equal_success_by_builtin_reason(
            left,
            right,
            line_file,
            "equality: 1^x = 1",
        )))
    }

    // Zero as a base stays zero for positive exponents: `0^x = 0` when `x > 0`.
    // This intentionally does not cover the zeroth power convention `0^0 = 1`.
    // Example: `forall x R_pos: 0^x = 0`.
    pub(crate) fn try_verify_zero_pow_positive_exponent_identity(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let pow = if Self::obj_is_builtin_literal_zero(left) {
            match right {
                Obj::Pow(p) => p,
                _ => return Ok(None),
            }
        } else if Self::obj_is_builtin_literal_zero(right) {
            match left {
                Obj::Pow(p) => p,
                _ => return Ok(None),
            }
        } else {
            return Ok(None);
        };
        if !Self::obj_is_builtin_literal_zero(pow.base.as_ref()) {
            return Ok(None);
        }

        let positive_exponent: AtomicFact = GreaterFact::new(
            (*pow.exponent).clone(),
            Self::literal_zero_obj_for_abs_builtin(),
            line_file.clone(),
        )
        .into();
        let positive_result = self.verify_non_equational_known_then_builtin_rules_only(
            &positive_exponent,
            verify_state,
        )?;
        if !positive_result.is_true() {
            return Ok(None);
        }

        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                EqualFact::new(left.clone(), right.clone(), line_file).into(),
                "equality: 0^x = 0 for x > 0".to_string(),
                vec![positive_result],
            )
            .into(),
        ))
    }
}
