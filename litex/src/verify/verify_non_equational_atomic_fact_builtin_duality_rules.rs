use crate::prelude::*;

impl Runtime {
    /// Verify subset by duality: `a subset b` iff `b superset a`.
    pub(crate) fn verify_subset_fact_with_builtin_rules(
        &mut self,
        subset_fact: &SubsetFact,
        _verify_state: &VerifyState,
    ) -> Result<NonErrStmtExecResult, VerifyError> {
        let converted_superset_fact = AtomicFact::SupersetFact(SupersetFact::new(
            subset_fact.right.clone(),
            subset_fact.left.clone(),
            subset_fact.line_file,
        ));
        let verify_result = self
            .verify_non_equational_atomic_fact_with_known_atomic_non_equational_facts(
                &converted_superset_fact,
            )?;
        if verify_result.is_true() {
            Ok(NonErrStmtExecResult::FactVerifiedByBuiltinRules(
                FactVerifiedByBuiltinRules::new(
                    Fact::AtomicFact(AtomicFact::SubsetFact(subset_fact.clone())),
                    "subset_superset_duality".to_string(),
                    InferResult::new(),
                ),
            ))
        } else {
            Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()))
        }
    }

    /// Verify superset by duality: `a superset b` iff `b subset a`.
    pub(crate) fn verify_superset_fact_with_builtin_rules(
        &mut self,
        superset_fact: &SupersetFact,
        _verify_state: &VerifyState,
    ) -> Result<NonErrStmtExecResult, VerifyError> {
        let converted_subset_fact = AtomicFact::SubsetFact(SubsetFact::new(
            superset_fact.right.clone(),
            superset_fact.left.clone(),
            superset_fact.line_file,
        ));
        let verify_result = self
            .verify_non_equational_atomic_fact_with_known_atomic_non_equational_facts(
                &converted_subset_fact,
            )?;
        if verify_result.is_true() {
            Ok(NonErrStmtExecResult::FactVerifiedByBuiltinRules(
                FactVerifiedByBuiltinRules::new(
                    Fact::AtomicFact(AtomicFact::SupersetFact(superset_fact.clone())),
                    "subset_superset_duality".to_string(),
                    InferResult::new(),
                ),
            ))
        } else {
            Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()))
        }
    }

    /// Verify `not subset` by converting to the dual `not superset`.
    pub(crate) fn verify_not_subset_fact_with_builtin_rules(
        &mut self,
        not_subset_fact: &NotSubsetFact,
        _verify_state: &VerifyState,
    ) -> Result<NonErrStmtExecResult, VerifyError> {
        let converted_not_superset_fact = AtomicFact::NotSupersetFact(NotSupersetFact::new(
            not_subset_fact.right.clone(),
            not_subset_fact.left.clone(),
            not_subset_fact.line_file,
        ));
        let verify_result = self
            .verify_non_equational_atomic_fact_with_known_atomic_non_equational_facts(
                &converted_not_superset_fact,
            )?;
        if verify_result.is_true() {
            Ok(NonErrStmtExecResult::FactVerifiedByBuiltinRules(
                FactVerifiedByBuiltinRules::new(
                    Fact::AtomicFact(AtomicFact::NotSubsetFact(not_subset_fact.clone())),
                    "subset_superset_duality".to_string(),
                    InferResult::new(),
                ),
            ))
        } else {
            Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()))
        }
    }

    /// Verify `not superset` by converting to the dual `not subset`.
    pub(crate) fn verify_not_superset_fact_with_builtin_rules(
        &mut self,
        not_superset_fact: &NotSupersetFact,
        _verify_state: &VerifyState,
    ) -> Result<NonErrStmtExecResult, VerifyError> {
        let converted_not_subset_fact = AtomicFact::NotSubsetFact(NotSubsetFact::new(
            not_superset_fact.right.clone(),
            not_superset_fact.left.clone(),
            not_superset_fact.line_file,
        ));
        let verify_result = self
            .verify_non_equational_atomic_fact_with_known_atomic_non_equational_facts(
                &converted_not_subset_fact,
            )?;
        if verify_result.is_true() {
            Ok(NonErrStmtExecResult::FactVerifiedByBuiltinRules(
                FactVerifiedByBuiltinRules::new(
                    Fact::AtomicFact(AtomicFact::NotSupersetFact(not_superset_fact.clone())),
                    "subset_superset_duality".to_string(),
                    InferResult::new(),
                ),
            ))
        } else {
            Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()))
        }
    }

    /// Verify `not (a < b)` by using `a >= b`.
    pub(crate) fn verify_not_less_fact_with_builtin_rules(
        &mut self,
        not_less_fact: &NotLessFact,
        _verify_state: &VerifyState,
    ) -> Result<NonErrStmtExecResult, VerifyError> {
        let counterpart_fact = AtomicFact::GreaterEqualFact(GreaterEqualFact::new(
            not_less_fact.left.clone(),
            not_less_fact.right.clone(),
            not_less_fact.line_file,
        ));
        self.verify_duality_atomic_fact_by_known_counterpart(
            &AtomicFact::NotLessFact(not_less_fact.clone()),
            &counterpart_fact,
            "real_order_negation_duality",
        )
    }

    /// Verify `not (a > b)` by using `a <= b`.
    pub(crate) fn verify_not_greater_fact_with_builtin_rules(
        &mut self,
        not_greater_fact: &NotGreaterFact,
        _verify_state: &VerifyState,
    ) -> Result<NonErrStmtExecResult, VerifyError> {
        let counterpart_fact = AtomicFact::LessEqualFact(LessEqualFact::new(
            not_greater_fact.left.clone(),
            not_greater_fact.right.clone(),
            not_greater_fact.line_file,
        ));
        self.verify_duality_atomic_fact_by_known_counterpart(
            &AtomicFact::NotGreaterFact(not_greater_fact.clone()),
            &counterpart_fact,
            "real_order_negation_duality",
        )
    }

    pub(crate) fn verify_not_less_equal_fact_with_builtin_rules(
        &mut self,
        not_less_equal_fact: &NotLessEqualFact,
        _verify_state: &VerifyState,
    ) -> Result<NonErrStmtExecResult, VerifyError> {
        let counterpart_fact = AtomicFact::GreaterFact(GreaterFact::new(
            not_less_equal_fact.left.clone(),
            not_less_equal_fact.right.clone(),
            not_less_equal_fact.line_file,
        ));
        self.verify_duality_atomic_fact_by_known_counterpart(
            &AtomicFact::NotLessEqualFact(not_less_equal_fact.clone()),
            &counterpart_fact,
            "real_order_negation_duality",
        )
    }

    pub(crate) fn verify_not_greater_equal_fact_with_builtin_rules(
        &mut self,
        not_greater_equal_fact: &NotGreaterEqualFact,
        _verify_state: &VerifyState,
    ) -> Result<NonErrStmtExecResult, VerifyError> {
        let counterpart_fact = AtomicFact::LessFact(LessFact::new(
            not_greater_equal_fact.left.clone(),
            not_greater_equal_fact.right.clone(),
            not_greater_equal_fact.line_file,
        ));
        self.verify_duality_atomic_fact_by_known_counterpart(
            &AtomicFact::NotGreaterEqualFact(not_greater_equal_fact.clone()),
            &counterpart_fact,
            "real_order_negation_duality",
        )
    }

    fn verify_duality_atomic_fact_by_known_counterpart(
        &mut self,
        current_fact: &AtomicFact,
        counterpart_fact: &AtomicFact,
        builtin_rule_name: &str,
    ) -> Result<NonErrStmtExecResult, VerifyError> {
        let counterpart_verify_result = self
            .verify_non_equational_atomic_fact_with_known_atomic_non_equational_facts(
                counterpart_fact,
            )?;
        if counterpart_verify_result.is_true() {
            Ok(NonErrStmtExecResult::FactVerifiedByBuiltinRules(
                FactVerifiedByBuiltinRules::new(
                    Fact::AtomicFact(current_fact.clone()),
                    builtin_rule_name.to_string(),
                    InferResult::new(),
                ),
            ))
        } else {
            Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()))
        }
    }

    /// Verify order facts by either direct number calculation or negation duality.
    pub(crate) fn verify_order_or_negation_fact_with_builtin_duality_and_number_compare(
        &mut self,
        current_fact: &AtomicFact,
        counterpart_fact: &AtomicFact,
    ) -> Result<NonErrStmtExecResult, VerifyError> {
        let number_compare_result = self.verify_number_comparison_builtin_rule(current_fact);
        if let Some(true) = number_compare_result {
            return Ok(NonErrStmtExecResult::FactVerifiedByBuiltinRules(
                FactVerifiedByBuiltinRules::new(
                    Fact::AtomicFact(current_fact.clone()),
                    "number comparison".to_string(),
                    InferResult::new(),
                ),
            ));
        }
        self.verify_duality_atomic_fact_by_known_counterpart(
            current_fact,
            counterpart_fact,
            "real_order_negation_duality",
        )
    }
}
