use crate::prelude::*;

impl Runtime {
    /// Verify subset by duality: `a subset b` iff `b superset a`.
    pub fn verify_subset_fact_with_builtin_rules(
        &mut self,
        subset_fact: &SubsetFact,
        builtin_state: &mut BuiltinRuleVerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        // Fundamental set containments follow directly from membership definitions.
        // Examples: `intersect(A, B) $subset A`, `A $subset union(A, B)`.
        let elementary_set_subset_reason = match (&subset_fact.left, &subset_fact.right) {
            (Obj::Intersect(intersect), right)
                if objs_equal_with_nested_binder_alpha_equivalence(&intersect.left, right)
                    || objs_equal_with_nested_binder_alpha_equivalence(&intersect.right, right) =>
            {
                Some("intersection_subset_operand")
            }
            (left, Obj::Union(union))
                if objs_equal_with_nested_binder_alpha_equivalence(&union.left, left)
                    || objs_equal_with_nested_binder_alpha_equivalence(&union.right, left) =>
            {
                Some("operand_subset_union")
            }
            (Obj::SetMinus(set_minus), right)
                if objs_equal_with_nested_binder_alpha_equivalence(&set_minus.left, right) =>
            {
                Some("set_minus_subset_left_operand")
            }
            _ => None,
        };
        if let Some(reason) = elementary_set_subset_reason {
            return Ok(
                (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    subset_fact.clone().into(),
                    reason.to_string(),
                    Vec::new(),
                ))
                .into(),
            );
        }

        // Standard number sets form a fixed inclusion chain. Example: `N $subset R`.
        if let (Obj::StandardSet(left), Obj::StandardSet(right)) =
            (&subset_fact.left, &subset_fact.right)
        {
            if Self::standard_set_is_subset_eq(left, right) {
                return Ok(
                    (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        subset_fact.clone().into(),
                        "standard_set_subset".to_string(),
                        Vec::new(),
                    ))
                    .into(),
                );
            }
        }

        // Every set is a subset of itself, including alpha-equivalent function
        // sets such as `fn(x X) X $subset fn(y X) X`.
        if objs_equal_with_nested_binder_alpha_equivalence(&subset_fact.left, &subset_fact.right) {
            return Ok(
                (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    subset_fact.clone().into(),
                    "subset_superset_duality".to_string(),
                    Vec::new(),
                ))
                .into(),
            );
        }

        // Every finite real interval is a subset of R once its endpoints are
        // well-defined reals. Example: `'[a, b] $subset R`.
        if matches!(subset_fact.left, Obj::IntervalObj(_))
            && matches!(subset_fact.right, Obj::StandardSet(StandardSet::R))
        {
            return Ok(
                (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    subset_fact.clone().into(),
                    "real_interval_subset_R".to_string(),
                    Vec::new(),
                ))
                .into(),
            );
        }

        // The range of `f : ... -> T` is a subset of `T`, and of any known superset of `T`.
        // Example: `have f fn(x S) T` proves `fn_range(f) $subset T`.
        if let Obj::FnRange(fn_range) = &subset_fact.left {
            if let Some(body) = self.get_fn_range_function_body(&fn_range.function) {
                let ret_subset: AtomicFact = SubsetFact::new(
                    body.ret_set.as_ref().clone(),
                    subset_fact.right.clone(),
                    subset_fact.line_file.clone(),
                )
                .into();
                let ret_subset_result =
                    self.verify_builtin_rule_premise(&ret_subset, builtin_state)?;
                if ret_subset_result.is_true() {
                    return Ok(
                        (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                            subset_fact.clone().into(),
                            "fn_range_subset_codomain".to_string(),
                            vec![ret_subset_result],
                        ))
                        .into(),
                    );
                }
            }
        }

        let converted_superset_fact = SupersetFact::new(
            subset_fact.right.clone(),
            subset_fact.left.clone(),
            subset_fact.line_file.clone(),
        )
        .into();
        let verify_result = self
            .verify_non_equational_atomic_fact_with_known_atomic_facts(&converted_superset_fact)?;
        if verify_result.is_true() {
            Ok(
                (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    subset_fact.clone().into(),
                    "subset_superset_duality".to_string(),
                    Vec::new(),
                ))
                .into(),
            )
        } else {
            Ok((StmtUnknown::new()).into())
        }
    }

    /// Verify superset by duality: `a superset b` iff `b subset a`.
    pub fn verify_superset_fact_with_builtin_rules(
        &mut self,
        superset_fact: &SupersetFact,
        _builtin_state: &mut BuiltinRuleVerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        // Standard number sets form a fixed inclusion chain. Example: `R $supset N`.
        if let (Obj::StandardSet(left), Obj::StandardSet(right)) =
            (&superset_fact.left, &superset_fact.right)
        {
            if Self::standard_set_is_subset_eq(right, left) {
                return Ok(
                    (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        superset_fact.clone().into(),
                        "standard_set_superset".to_string(),
                        Vec::new(),
                    ))
                    .into(),
                );
            }
        }

        // Every set is a superset of itself, including alpha-equivalent
        // function sets such as `fn(x X) X $supset fn(y X) X`.
        if objs_equal_with_nested_binder_alpha_equivalence(
            &superset_fact.left,
            &superset_fact.right,
        ) {
            return Ok(
                (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    superset_fact.clone().into(),
                    "subset_superset_duality".to_string(),
                    Vec::new(),
                ))
                .into(),
            );
        }
        let converted_subset_fact = SubsetFact::new(
            superset_fact.right.clone(),
            superset_fact.left.clone(),
            superset_fact.line_file.clone(),
        )
        .into();
        let verify_result =
            self.verify_non_equational_atomic_fact_with_known_atomic_facts(&converted_subset_fact)?;
        if verify_result.is_true() {
            Ok(
                (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    superset_fact.clone().into(),
                    "subset_superset_duality".to_string(),
                    Vec::new(),
                ))
                .into(),
            )
        } else {
            Ok((StmtUnknown::new()).into())
        }
    }

    /// Verify `not subset` by converting to the dual `not superset`.
    pub fn verify_not_subset_fact_with_builtin_rules(
        &mut self,
        not_subset_fact: &NotSubsetFact,
        _builtin_state: &mut BuiltinRuleVerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let converted_not_superset_fact = NotSupersetFact::new(
            not_subset_fact.right.clone(),
            not_subset_fact.left.clone(),
            not_subset_fact.line_file.clone(),
        )
        .into();
        let verify_result = self.verify_non_equational_atomic_fact_with_known_atomic_facts(
            &converted_not_superset_fact,
        )?;
        if verify_result.is_true() {
            Ok(
                (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    not_subset_fact.clone().into(),
                    "subset_superset_duality".to_string(),
                    Vec::new(),
                ))
                .into(),
            )
        } else {
            Ok((StmtUnknown::new()).into())
        }
    }

    /// Verify `not superset` by converting to the dual `not subset`.
    pub fn verify_not_superset_fact_with_builtin_rules(
        &mut self,
        not_superset_fact: &NotSupersetFact,
        _builtin_state: &mut BuiltinRuleVerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let converted_not_subset_fact = NotSubsetFact::new(
            not_superset_fact.right.clone(),
            not_superset_fact.left.clone(),
            not_superset_fact.line_file.clone(),
        )
        .into();
        let verify_result = self.verify_non_equational_atomic_fact_with_known_atomic_facts(
            &converted_not_subset_fact,
        )?;
        if verify_result.is_true() {
            Ok(
                (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    not_superset_fact.clone().into(),
                    "subset_superset_duality".to_string(),
                    Vec::new(),
                ))
                .into(),
            )
        } else {
            Ok((StmtUnknown::new()).into())
        }
    }
}
