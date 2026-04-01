use crate::prelude::*;

impl Runtime {
    fn return_err_if_forall_fact_with_iff_then_or_iff_clauses_miss_some_parameter_name(
        forall_fact_with_iff: &ForallFactWithIff,
    ) -> Result<(), RuntimeErrorStruct> {
        let coverage_error_detail_lines =
            forall_fact_with_iff.error_messages_if_forall_param_missing_in_then_or_iff_clause();
        if coverage_error_detail_lines.is_empty() {
            return Ok(());
        }
        Err(RuntimeErrorStruct::new(
            None,
            format!(
                "failed to store forall fact with iff:\n{}",
                coverage_error_detail_lines.join("\n")
            ),
            forall_fact_with_iff.line_file,
            None,
        ))
    }

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

    fn store_forall_fact_without_well_defined_verified_and_infer(
        &mut self,
        forall_fact: ForallFact,
    ) -> Result<InferResult, RuntimeErrorStruct> {
        return_err_if_forall_fact_then_or_iff_clauses_miss_some_parameter_name(&forall_fact)?;
        self.store_whole_fact_update_cache_known_fact_and_infer(Fact::ForallFact(forall_fact))
    }

    fn store_forall_fact_with_iff_without_well_defined_verified_and_infer(
        &mut self,
        forall_fact_with_iff: ForallFactWithIff,
    ) -> Result<InferResult, RuntimeErrorStruct> {
        Self::return_err_if_forall_fact_with_iff_then_or_iff_clauses_miss_some_parameter_name(
            &forall_fact_with_iff,
        )?;
        self.store_whole_fact_update_cache_known_fact_and_infer(Fact::ForallFactWithIff(
            forall_fact_with_iff,
        ))
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
            RuntimeErrorStruct::new_with_msg_previous_error(
                format!("infer error: {}", e),
                Some(e.into()),
            )
        })?;
        Ok(infer_result)
    }

    pub fn store_and_chain_atomic_fact_without_well_defined_verified_and_infer(
        &mut self,
        fact: AndChainAtomicFact,
    ) -> Result<InferResult, RuntimeErrorStruct> {
        let line_file = fact.line_file();
        let fact_string: FactString = fact.to_string();
        let fact_for_infer = fact.to_fact();
        self.top_level_env().store_and_chain_atomic_fact(fact)?;

        self.top_level_env()
            .store_fact_to_cache_known_fact(fact_string, line_file)?;

        let infer_result = self.infer(&fact_for_infer).map_err(|e| {
            RuntimeErrorStruct::new_with_msg_previous_error(
                format!("infer error: {}", e),
                Some(e.into()),
            )
        })?;
        Ok(infer_result)
    }

    pub fn store_atomic_fact_without_well_defined_verified_and_infer(
        &mut self,
        fact: AtomicFact,
    ) -> Result<InferResult, RuntimeErrorStruct> {
        let line_file = fact.line_file();
        let fact_string: FactString = fact.to_string();
        let infer_wrapped_fact = Fact::AtomicFact(fact.clone());
        self.top_level_env().store_atomic_fact(fact)?;

        self.top_level_env()
            .store_fact_to_cache_known_fact(fact_string, line_file)?;

        let infer_result = self.infer(&infer_wrapped_fact).map_err(|e| {
            RuntimeErrorStruct::new_with_msg_previous_error(
                format!("infer error: {}", e),
                Some(e.into()),
            )
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
                    Some(e.into()),
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
                    Some(e.into()),
                )
            })?;
        Ok(infer_result)
    }
}

fn return_err_if_forall_fact_then_or_iff_clauses_miss_some_parameter_name(
    forall_fact: &ForallFact,
) -> Result<(), RuntimeErrorStruct> {
    let coverage_error_detail_lines =
        forall_fact.error_messages_if_forall_param_missing_in_some_then_clause();
    if coverage_error_detail_lines.is_empty() {
        return Ok(());
    }
    Err(RuntimeErrorStruct::new(
        None,
        format!(
            "failed to store forall fact:\n{}",
            coverage_error_detail_lines.join("\n")
        ),
        forall_fact.line_file,
        None,
    ))
}
