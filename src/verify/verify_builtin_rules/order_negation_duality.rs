use crate::prelude::*;

impl Runtime {
    /// Verify `not (a < b)` by using `a >= b`.
    pub(crate) fn verify_not_less_fact_with_builtin_rules(
        &mut self,
        not_less_fact: &NotLessFact,
        _verify_state: &VerifyState,
    ) -> Result<StmtExecResult, RuntimeError> {
        let counterpart_fact = AtomicFact::LessEqualFact(LessEqualFact::new(
            not_less_fact.right.clone(),
            not_less_fact.left.clone(),
            not_less_fact.line_file.clone(),
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
    ) -> Result<StmtExecResult, RuntimeError> {
        if not_greater_fact.left.to_string() == not_greater_fact.right.to_string() {
            return Ok(StmtExecResult::FactualStmtSuccess(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    Fact::AtomicFact(AtomicFact::NotGreaterFact(not_greater_fact.clone())),
                    format!(
                        "{} = {}",
                        not_greater_fact.left.to_string(),
                        not_greater_fact.right.to_string()
                    ),
                    Vec::new(),
                ),
            ));
        }

        let counterpart_fact = AtomicFact::LessEqualFact(LessEqualFact::new(
            not_greater_fact.left.clone(),
            not_greater_fact.right.clone(),
            not_greater_fact.line_file.clone(),
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
    ) -> Result<StmtExecResult, RuntimeError> {
        if not_less_equal_fact.left.to_string() == not_less_equal_fact.right.to_string() {
            return Ok(StmtExecResult::FactualStmtSuccess(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    Fact::AtomicFact(AtomicFact::NotLessEqualFact(not_less_equal_fact.clone())),
                    format!(
                        "{} = {}",
                        not_less_equal_fact.left.to_string(),
                        not_less_equal_fact.right.to_string()
                    ),
                    Vec::new(),
                ),
            ));
        }

        let counterpart_fact = AtomicFact::LessFact(LessFact::new(
            not_less_equal_fact.right.clone(),
            not_less_equal_fact.left.clone(),
            not_less_equal_fact.line_file.clone(),
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
    ) -> Result<StmtExecResult, RuntimeError> {
        let counterpart_fact = AtomicFact::LessFact(LessFact::new(
            not_greater_equal_fact.left.clone(),
            not_greater_equal_fact.right.clone(),
            not_greater_equal_fact.line_file.clone(),
        ));
        self.verify_duality_atomic_fact_by_known_counterpart(
            &AtomicFact::NotGreaterEqualFact(not_greater_equal_fact.clone()),
            &counterpart_fact,
            "real_order_negation_duality",
        )
    }

    pub(crate) fn verify_duality_atomic_fact_by_known_counterpart(
        &mut self,
        current_fact: &AtomicFact,
        counterpart_fact: &AtomicFact,
        builtin_rule_name: &str,
    ) -> Result<StmtExecResult, RuntimeError> {
        let counterpart_verify_result = self
            .verify_non_equational_atomic_fact_with_known_atomic_non_equational_facts(
                counterpart_fact,
            )?;
        if counterpart_verify_result.is_true() {
            Ok(StmtExecResult::FactualStmtSuccess(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    Fact::AtomicFact(current_fact.clone()),
                    builtin_rule_name.to_string(),
                    Vec::new(),
                ),
            ))
        } else {
            Ok(StmtExecResult::StmtUnknown(StmtUnknown::new()))
        }
    }
}
