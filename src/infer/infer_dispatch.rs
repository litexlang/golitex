use crate::prelude::*;

impl Runtime {
    /// Dispatch infer by fact kind.
    /// Example: `a $subset b` enters atomic infer branch.
    pub fn infer(&mut self, fact: &Fact) -> Result<SuccessInferResult, RuntimeError> {
        match fact {
            Fact::AtomicFact(atomic_fact) => self.infer_atomic_fact(atomic_fact),
            Fact::ExistFact(exist_fact) => self.infer_exist_fact(exist_fact),
            Fact::OrFact(or_fact) => self.infer_or_fact(or_fact),
            Fact::AndFact(and_fact) => self.infer_and_fact(and_fact),
            Fact::ChainFact(chain_fact) => self.infer_chain_fact(chain_fact),
            Fact::ForallFact(forall_fact) => self.infer_forall_fact(forall_fact),
            Fact::ForallFactWithIff(forall_fact_with_iff) => {
                self.infer_forall_fact_with_iff(forall_fact_with_iff)
            }
            Fact::NotForall(not_forall) => self.infer_not_forall_fact(not_forall),
        }
    }

    pub fn infer_exist_or_and_chain_atomic_fact(
        &mut self,
        fact: &ExistOrAndChainAtomicFact,
    ) -> Result<SuccessInferResult, RuntimeError> {
        match fact {
            ExistOrAndChainAtomicFact::AtomicFact(atomic_fact) => {
                self.infer_atomic_fact(atomic_fact)
            }
            ExistOrAndChainAtomicFact::AndFact(and_fact) => self.infer_and_fact(and_fact),
            ExistOrAndChainAtomicFact::ChainFact(chain_fact) => self.infer_chain_fact(chain_fact),
            ExistOrAndChainAtomicFact::OrFact(or_fact) => self.infer_or_fact(or_fact),
            ExistOrAndChainAtomicFact::ExistFact(exist_fact) => self.infer_exist_fact(exist_fact),
        }
    }

    pub fn infer_quantifier_free_fact(
        &mut self,
        fact: &QuantifierFreeFact,
    ) -> Result<SuccessInferResult, RuntimeError> {
        match fact {
            QuantifierFreeFact::AtomicFact(atomic_fact) => self.infer_atomic_fact(atomic_fact),
            QuantifierFreeFact::AndFact(and_fact) => self.infer_and_fact(and_fact),
            QuantifierFreeFact::ChainFact(chain_fact) => self.infer_chain_fact(chain_fact),
            QuantifierFreeFact::OrFact(or_fact) => self.infer_or_fact(or_fact),
        }
    }

    fn infer_exist_fact(
        &mut self,
        exist_fact: &ExistFactEnum,
    ) -> Result<SuccessInferResult, RuntimeError> {
        let mut out = SuccessInferResult::new();
        if exist_fact.is_exist_unique() && exist_fact.typed_parameters().number_of_params() > 0 {
            // Infer uniqueness from a stored `exist!`.
            // Example: `exist! c Z, d N+ st {p(c, d)}` infers
            // `forall c1 Z, d1 N+, c2 Z, d2 N+: p(c1,d1) p(c2,d2) => c1=c2 and d1=d2`.
            let uniq = self.build_exist_unique_component_uniqueness_forall_fact(exist_fact)?;
            if uniq
                .error_messages_if_forall_param_missing_in_some_then_clause()
                .is_empty()
            {
                out.new_fact(&uniq.clone().into());
            }
            out.new_infer_result_inside(
                self.store_forall_fact_without_well_defined_verified_and_infer(uniq)?,
            );
        } else if exist_fact.is_not_exist() && exist_fact.typed_parameters().number_of_params() > 0
        {
            let forall = self.build_not_exist_demorgan_forall_fact(exist_fact)?;
            if forall
                .error_messages_if_forall_param_missing_in_some_then_clause()
                .is_empty()
            {
                out.new_fact(&forall.clone().into());
            }
            out.new_infer_result_inside(
                self.store_forall_fact_without_well_defined_verified_and_infer(forall)?,
            );
        }
        Ok(out)
    }

    fn infer_or_fact(&mut self, _or_fact: &OrFact) -> Result<SuccessInferResult, RuntimeError> {
        Ok(SuccessInferResult::new())
    }

    fn infer_and_fact(&mut self, and_fact: &AndFact) -> Result<SuccessInferResult, RuntimeError> {
        let source_fact: Fact = and_fact.clone().into();
        let component_count = and_fact.facts.len();
        let mut result = SuccessInferResult::new();
        for (component_index, component) in and_fact.facts.iter().enumerate() {
            let component_fact: Fact = component.clone().into();
            let component_infers = self
                .store_without_well_defined_verification_and_infer_with_reason(
                    component_fact.clone(),
                    InferReason::InferredFact,
                )?;
            result.add_rule_application_preserving_conclusion_result_structure(
                InferRule::ConjunctionImpliesComponent(ConjunctionImpliesComponentInferRule {
                    component_index,
                    component_count,
                }),
                vec![source_fact.clone()],
                vec![SuccessStoreFactResult::new(
                    component_fact,
                    component_infers,
                )],
            );
        }
        Ok(result)
    }

    fn infer_chain_fact(
        &mut self,
        chain_fact: &ChainFact,
    ) -> Result<SuccessInferResult, RuntimeError> {
        let atomic_facts = match chain_fact.facts_with_order_transitive_closure() {
            Ok(v) => v,
            Err(_) => return Ok(SuccessInferResult::new()),
        };
        let mut infer_result = SuccessInferResult::new();
        for atomic_fact in atomic_facts {
            infer_result.new_infer_result_inside(self.infer_atomic_fact(&atomic_fact)?);
        }
        Ok(infer_result)
    }

    // Do not record the whole forall as an inferred fact; inner then-clauses are stored separately.
    fn infer_forall_fact(
        &mut self,
        _forall_fact: &ForallFact,
    ) -> Result<SuccessInferResult, RuntimeError> {
        Ok(SuccessInferResult::new())
    }

    fn infer_forall_fact_with_iff(
        &mut self,
        _forall_fact_with_iff: &ForallFactWithIff,
    ) -> Result<SuccessInferResult, RuntimeError> {
        Ok(SuccessInferResult::new())
    }
}

#[cfg(test)]
#[path = "../../tests/unit/infer/infer_dispatch/conjunction_component_inference_result_tests.rs"]
mod conjunction_component_inference_result_tests;
