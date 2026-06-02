use crate::prelude::*;

impl Runtime {
    /// Verify subset by duality: `a subset b` iff `b superset a`.
    pub fn verify_subset_fact_with_builtin_rules(
        &mut self,
        subset_fact: &SubsetFact,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
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

        if subset_fact.left.to_string() == subset_fact.right.to_string() {
            return Ok(
                (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    subset_fact.clone().into(),
                    "subset_superset_duality".to_string(),
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
                let ret_subset_result = self.verify_non_equational_known_then_builtin_rules_only(
                    &ret_subset,
                    verify_state,
                )?;
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
        _verify_state: &VerifyState,
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

        if superset_fact.left.to_string() == superset_fact.right.to_string() {
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
        _verify_state: &VerifyState,
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
        _verify_state: &VerifyState,
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
