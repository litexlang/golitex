use super::*;

impl Runtime {
    /// `(x mod m) mod m = x mod m` when the nested `%` uses the same modulus as the outer `%`.
    ///
    /// Used to match residues after reducing summands: e.g. prove `X % Z = (X % Z) % Z` so
    /// `(X+Y)%Z = ((X%Z)+(Y%Z))%Z` can close via congruence.
    pub(crate) fn try_verify_mod_nested_same_modulus_absorption(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        for (side_nested, side_simple) in [(left, right), (right, left)] {
            let Obj::Mod(outer) = side_nested else {
                continue;
            };
            let Obj::Mod(inner) = outer.left.as_ref() else {
                continue;
            };
            let Obj::Mod(simple) = side_simple else {
                continue;
            };
            if !self
                .verify_objs_are_equal_in_equality_builtin(
                    outer.right.as_ref(),
                    inner.right.as_ref(),
                    line_file.clone(),
                    verify_state,
                )?
                .is_true()
            {
                continue;
            }
            if !self
                .verify_objs_are_equal_in_equality_builtin(
                    outer.right.as_ref(),
                    simple.right.as_ref(),
                    line_file.clone(),
                    verify_state,
                )?
                .is_true()
            {
                continue;
            }
            if !self
                .verify_objs_are_equal_in_equality_builtin(
                    inner.left.as_ref(),
                    simple.left.as_ref(),
                    line_file.clone(),
                    verify_state,
                )?
                .is_true()
            {
                continue;
            }
            return Ok(Some(factual_equal_success_by_builtin_reason(
                left,
                right,
                line_file,
                "equality: nested mod with same modulus absorbs inner mod",
            )));
        }
        Ok(None)
    }

    // a % m = (b % m) % m reduces to a % m = b % m (same m); the inner equality must be known-only.
    pub(crate) fn try_verify_mod_peel_nested_same_modulus(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let (Obj::Mod(lm), Obj::Mod(rm)) = (left, right) else {
            return Ok(None);
        };
        if !self
            .verify_objs_are_equal_in_equality_builtin(
                lm.right.as_ref(),
                rm.right.as_ref(),
                line_file.clone(),
                verify_state,
            )?
            .is_true()
        {
            return Ok(None);
        }
        let modulus = lm.right.as_ref();

        if let Obj::Mod(r_inner) = rm.left.as_ref() {
            if self
                .verify_objs_are_equal_in_equality_builtin(
                    r_inner.right.as_ref(),
                    modulus,
                    line_file.clone(),
                    verify_state,
                )?
                .is_true()
            {
                let lhs: Obj = Mod::new((*lm.left).clone(), (*lm.right).clone()).into();
                let rhs: Obj = Mod::new((*r_inner.left).clone(), (*lm.right).clone()).into();
                if self
                    .verify_objs_are_equal_in_equality_builtin(
                        &lhs,
                        &rhs,
                        line_file.clone(),
                        verify_state,
                    )?
                    .is_true()
                {
                    return Ok(Some(factual_equal_success_by_builtin_reason(
                        left,
                        right,
                        line_file,
                        "equality: mod — peel outer nested % m to reuse known residue equality",
                    )));
                }
            }
        }

        if let Obj::Mod(l_inner) = lm.left.as_ref() {
            if self
                .verify_objs_are_equal_in_equality_builtin(
                    l_inner.right.as_ref(),
                    modulus,
                    line_file.clone(),
                    verify_state,
                )?
                .is_true()
            {
                let lhs: Obj = Mod::new((*l_inner.left).clone(), (*lm.right).clone()).into();
                let rhs: Obj = Mod::new((*rm.left).clone(), (*lm.right).clone()).into();
                if self
                    .verify_objs_are_equal_in_equality_builtin(
                        &lhs,
                        &rhs,
                        line_file.clone(),
                        verify_state,
                    )?
                    .is_true()
                {
                    return Ok(Some(factual_equal_success_by_builtin_reason(
                        left,
                        right,
                        line_file,
                        "equality: mod — peel outer nested % m to reuse known residue equality",
                    )));
                }
            }
        }

        Ok(None)
    }

    /// If `% m` agrees on both sides, congruence for `+`, `-`, `*` on integers: reduce to two residue
    /// equalities.
    ///
    /// Example: `(x + y) % m = (x' + y') % m` from `(x % m) = (x' % m)` and `(y % m) = (y' % m)`.
    pub(crate) fn try_verify_mod_congruence_from_inner_binary(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let (Obj::Mod(lm), Obj::Mod(rm)) = (left, right) else {
            return Ok(None);
        };
        if !self
            .verify_objs_are_equal_in_equality_builtin(
                lm.right.as_ref(),
                rm.right.as_ref(),
                line_file.clone(),
                verify_state,
            )?
            .is_true()
        {
            return Ok(None);
        }
        let mut pair_ok = |a: &Obj, b: &Obj| -> Result<bool, RuntimeError> {
            let l: Obj = Mod::new(a.clone(), (*lm.right).clone()).into();
            let r: Obj = Mod::new(b.clone(), (*rm.right).clone()).into();
            Ok(self
                .verify_objs_are_equal_in_equality_builtin(&l, &r, line_file.clone(), verify_state)?
                .is_true())
        };
        let ok = match (lm.left.as_ref(), rm.left.as_ref()) {
            (Obj::Add(la), Obj::Add(ra)) => {
                pair_ok(la.left.as_ref(), ra.left.as_ref())?
                    && pair_ok(la.right.as_ref(), ra.right.as_ref())?
            }
            (Obj::Sub(ls), Obj::Sub(rs)) => {
                pair_ok(ls.left.as_ref(), rs.left.as_ref())?
                    && pair_ok(ls.right.as_ref(), rs.right.as_ref())?
            }
            (Obj::Mul(lx), Obj::Mul(rx)) => {
                pair_ok(lx.left.as_ref(), rx.left.as_ref())?
                    && pair_ok(lx.right.as_ref(), rx.right.as_ref())?
            }
            _ => return Ok(None),
        };
        if !ok {
            return Ok(None);
        }
        Ok(Some(factual_equal_success_by_builtin_reason(
            left,
            right,
            line_file,
            "equality: integer congruence — same modulus, residues for matching + / - / *",
        )))
    }
}
