use crate::prelude::*;

impl Runtime {
    /// Verify subset by duality: `a subset b` iff `b superset a`.
    pub(crate) fn verify_subset_fact_with_builtin_rules(
        &mut self,
        subset_fact: &SubsetFact,
        _verify_state: &VerifyState,
    ) -> Result<StmtExecResult, RuntimeError> {
        if subset_fact.left.to_string() == subset_fact.right.to_string() {
            return Ok(StmtExecResult::FactualStmtSuccess(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    Fact::AtomicFact(AtomicFact::SubsetFact(subset_fact.clone())),
                    "subset_superset_duality".to_string(),
                    Vec::new(),
                ),
            ));
        }

        let converted_superset_fact = AtomicFact::SupersetFact(SupersetFact::new(
            subset_fact.right.clone(),
            subset_fact.left.clone(),
            subset_fact.line_file.clone(),
        ));
        let verify_result = self
            .verify_non_equational_atomic_fact_with_known_atomic_non_equational_facts(
                &converted_superset_fact,
            )?;
        if verify_result.is_true() {
            Ok(StmtExecResult::FactualStmtSuccess(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    Fact::AtomicFact(AtomicFact::SubsetFact(subset_fact.clone())),
                    "subset_superset_duality".to_string(),
                    Vec::new(),
                ),
            ))
        } else {
            Ok(StmtExecResult::StmtUnknown(StmtUnknown::new()))
        }
    }

    /// Verify superset by duality: `a superset b` iff `b subset a`.
    pub(crate) fn verify_superset_fact_with_builtin_rules(
        &mut self,
        superset_fact: &SupersetFact,
        _verify_state: &VerifyState,
    ) -> Result<StmtExecResult, RuntimeError> {
        if superset_fact.left.to_string() == superset_fact.right.to_string() {
            return Ok(StmtExecResult::FactualStmtSuccess(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    Fact::AtomicFact(AtomicFact::SupersetFact(superset_fact.clone())),
                    "subset_superset_duality".to_string(),
                    Vec::new(),
                ),
            ));
        }
        let converted_subset_fact = AtomicFact::SubsetFact(SubsetFact::new(
            superset_fact.right.clone(),
            superset_fact.left.clone(),
            superset_fact.line_file.clone(),
        ));
        let verify_result = self
            .verify_non_equational_atomic_fact_with_known_atomic_non_equational_facts(
                &converted_subset_fact,
            )?;
        if verify_result.is_true() {
            Ok(StmtExecResult::FactualStmtSuccess(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    Fact::AtomicFact(AtomicFact::SupersetFact(superset_fact.clone())),
                    "subset_superset_duality".to_string(),
                    Vec::new(),
                ),
            ))
        } else {
            Ok(StmtExecResult::StmtUnknown(StmtUnknown::new()))
        }
    }

    /// Verify `not subset` by converting to the dual `not superset`.
    pub(crate) fn verify_not_subset_fact_with_builtin_rules(
        &mut self,
        not_subset_fact: &NotSubsetFact,
        _verify_state: &VerifyState,
    ) -> Result<StmtExecResult, RuntimeError> {
        let converted_not_superset_fact = AtomicFact::NotSupersetFact(NotSupersetFact::new(
            not_subset_fact.right.clone(),
            not_subset_fact.left.clone(),
            not_subset_fact.line_file.clone(),
        ));
        let verify_result = self
            .verify_non_equational_atomic_fact_with_known_atomic_non_equational_facts(
                &converted_not_superset_fact,
            )?;
        if verify_result.is_true() {
            Ok(StmtExecResult::FactualStmtSuccess(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    Fact::AtomicFact(AtomicFact::NotSubsetFact(not_subset_fact.clone())),
                    "subset_superset_duality".to_string(),
                    Vec::new(),
                ),
            ))
        } else {
            Ok(StmtExecResult::StmtUnknown(StmtUnknown::new()))
        }
    }

    /// Verify `not superset` by converting to the dual `not subset`.
    pub(crate) fn verify_not_superset_fact_with_builtin_rules(
        &mut self,
        not_superset_fact: &NotSupersetFact,
        _verify_state: &VerifyState,
    ) -> Result<StmtExecResult, RuntimeError> {
        let converted_not_subset_fact = AtomicFact::NotSubsetFact(NotSubsetFact::new(
            not_superset_fact.right.clone(),
            not_superset_fact.left.clone(),
            not_superset_fact.line_file.clone(),
        ));
        let verify_result = self
            .verify_non_equational_atomic_fact_with_known_atomic_non_equational_facts(
                &converted_not_subset_fact,
            )?;
        if verify_result.is_true() {
            Ok(StmtExecResult::FactualStmtSuccess(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    Fact::AtomicFact(AtomicFact::NotSupersetFact(not_superset_fact.clone())),
                    "subset_superset_duality".to_string(),
                    Vec::new(),
                ),
            ))
        } else {
            Ok(StmtExecResult::StmtUnknown(StmtUnknown::new()))
        }
    }
}
