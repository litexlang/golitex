use crate::prelude::*;
use std::collections::HashSet;

impl Runtime {
    pub fn store_fact_without_well_defined_verified_and_infer(
        &mut self,
        fact: Fact,
    ) -> Result<InferResult, RuntimeErrorStruct> {
        match fact {
            Fact::AtomicFact(_)
            | Fact::ExistFact(_)
            | Fact::OrFact(_)
            | Fact::AndFact(_)
            | Fact::ChainFact(_) => self.store_whole_fact_update_cache_known_fact_and_infer(fact),
            Fact::ForallFact(forall_fact) => {
                self.store_forall_fact_without_well_defined_verified_and_infer(forall_fact)
            }
            Fact::ForallFactWithIff(forall_fact_with_iff) => self
                .store_forall_fact_with_iff_without_well_defined_verified_and_infer(
                    forall_fact_with_iff,
                ),
        }
    }

    pub fn store_fact_without_forall_coverage_check_and_infer(
        &mut self,
        fact: Fact,
    ) -> Result<InferResult, RuntimeErrorStruct> {
        self.store_whole_fact_update_cache_known_fact_and_infer(fact)
    }

    fn store_forall_fact_without_well_defined_verified_and_infer(
        &mut self,
        mut forall_fact: ForallFact,
    ) -> Result<InferResult, RuntimeErrorStruct> {
        let coverage_error_detail_lines =
            forall_fact.error_messages_if_forall_param_missing_in_some_then_clause();

        if coverage_error_detail_lines.is_empty() {
            return self
                .store_whole_fact_update_cache_known_fact_and_infer(Fact::ForallFact(forall_fact));
        }

        let warning_msg = forall_fact_coverage_warn_after_drop_then(&coverage_error_detail_lines);
        let then_drop: HashSet<usize> = coverage_error_detail_lines
            .iter()
            .map(|(i, _)| *i)
            .collect();

        forall_fact.then_facts = forall_fact
            .then_facts
            .into_iter()
            .enumerate()
            .filter(|(i, _)| !then_drop.contains(i))
            .map(|(_, f)| f)
            .collect();

        if forall_fact.then_facts.is_empty() {
            let mut infer_result = InferResult::new();
            infer_result.new_with_msg(warning_msg);
            return Ok(infer_result);
        }

        let mut infer_result = InferResult::new();
        infer_result.new_with_msg(warning_msg);
        infer_result.new_infer_result_inside(
            self.store_whole_fact_update_cache_known_fact_and_infer(Fact::ForallFact(forall_fact))?,
        );
        Ok(infer_result)
    }

    fn store_forall_fact_with_iff_without_well_defined_verified_and_infer(
        &mut self,
        forall_fact_with_iff: ForallFactWithIff,
    ) -> Result<InferResult, RuntimeErrorStruct> {
        let (forall_then_implies_iff, forall_iff_implies_then) =
            forall_fact_with_iff.to_two_forall_facts();
        let mut infer_result = self
            .store_forall_fact_without_well_defined_verified_and_infer(forall_then_implies_iff)?;
        infer_result.new_infer_result_inside(
            self.store_forall_fact_without_well_defined_verified_and_infer(
                forall_iff_implies_then,
            )?,
        );
        Ok(infer_result)
    }

    fn store_whole_fact_update_cache_known_fact_and_infer(
        &mut self,
        fact: Fact,
    ) -> Result<InferResult, RuntimeErrorStruct> {
        let line_file = fact.line_file();
        let fact_string: FactString = fact.to_string();
        let fact_for_infer = fact.clone();
        self.top_level_env().store_fact(fact)?;

        self.top_level_env()
            .store_fact_to_cache_known_fact(fact_string, line_file)?;

        let infer_result = self.infer(&fact_for_infer).map_err(|e| {
            RuntimeErrorStruct::new_with_msg_previous_error(format!("infer error: {}", e), Some(e))
        })?;
        Ok(infer_result)
    }

    pub fn store_and_chain_atomic_fact_without_well_defined_verified_and_infer(
        &mut self,
        fact: AndChainAtomicFact,
    ) -> Result<InferResult, RuntimeErrorStruct> {
        let line_file = fact.line_file();
        let fact_string: FactString = fact.to_string();
        let fact_for_infer: Fact = fact.clone().into();
        self.top_level_env().store_and_chain_atomic_fact(fact)?;

        self.top_level_env()
            .store_fact_to_cache_known_fact(fact_string, line_file)?;

        let infer_result = self.infer(&fact_for_infer).map_err(|e| {
            RuntimeErrorStruct::new_with_msg_previous_error(format!("infer error: {}", e), Some(e))
        })?;
        Ok(infer_result)
    }

    pub fn store_atomic_fact_without_well_defined_verified_and_infer(
        &mut self,
        fact: AtomicFact,
    ) -> Result<InferResult, RuntimeErrorStruct> {
        let line_file = fact.line_file();
        let fact_string: FactString = fact.to_string();
        let infer_wrapped_fact: Fact = fact.clone().into();
        self.top_level_env().store_atomic_fact(fact)?;

        self.top_level_env()
            .store_fact_to_cache_known_fact(fact_string, line_file)?;

        let infer_result = self.infer(&infer_wrapped_fact).map_err(|e| {
            RuntimeErrorStruct::new_with_msg_previous_error(format!("infer error: {}", e), Some(e))
        })?;
        Ok(infer_result)
    }

    pub fn store_exist_or_and_chain_atomic_fact_without_well_defined_verified_and_infer(
        &mut self,
        fact: ExistOrAndChainAtomicFact,
    ) -> Result<InferResult, RuntimeErrorStruct> {
        let line_file = fact.line_file();
        let fact_string: FactString = fact.to_string();
        let fact_for_infer = fact.clone();
        self.top_level_env()
            .store_exist_or_and_chain_atomic_fact(fact)?;

        self.top_level_env()
            .store_fact_to_cache_known_fact(fact_string, line_file)?;

        let infer_result = self
            .infer_exist_or_and_chain_atomic_fact(&fact_for_infer)
            .map_err(|e| {
                RuntimeErrorStruct::new_with_msg_previous_error(
                    format!("infer error: {}", e),
                    Some(e),
                )
            })?;
        Ok(infer_result)
    }

    pub fn store_or_and_chain_atomic_fact_without_well_defined_verified_and_infer(
        &mut self,
        fact: OrAndChainAtomicFact,
    ) -> Result<InferResult, RuntimeErrorStruct> {
        let line_file = fact.line_file();
        let fact_string: FactString = fact.to_string();
        let fact_for_infer = fact.clone();
        self.top_level_env().store_or_and_chain_atomic_fact(fact)?;

        self.top_level_env()
            .store_fact_to_cache_known_fact(fact_string, line_file)?;

        let infer_result = self
            .infer_or_and_chain_atomic_fact(&fact_for_infer)
            .map_err(|e| {
                RuntimeErrorStruct::new_with_msg_previous_error(
                    format!("infer error: {}", e),
                    Some(e),
                )
            })?;
        Ok(infer_result)
    }
}

fn forall_fact_coverage_warn_after_drop_then(
    coverage_error_detail_lines: &[(usize, String)],
) -> String {
    let body = coverage_error_detail_lines
        .iter()
        .map(|(idx, msg)| format!("at index {}: {}", idx, msg))
        .collect::<Vec<_>>()
        .join("\n");
    format!(
        "Warning: forall missing forall parameter(s) in some then clause(s); dropped problematic clause(s):\n{}",
        body
    )
}
