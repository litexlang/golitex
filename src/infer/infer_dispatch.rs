use crate::prelude::*;

impl Runtime {
    /// Dispatch infer by fact kind.
    /// Example: `a $subset b` enters atomic infer branch.
    pub fn infer(&mut self, fact: &Fact) -> Result<InferResult, RuntimeError> {
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
    ) -> Result<InferResult, RuntimeError> {
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

    pub fn infer_or_and_chain_atomic_fact(
        &mut self,
        fact: &OrAndChainAtomicFact,
    ) -> Result<InferResult, RuntimeError> {
        match fact {
            OrAndChainAtomicFact::AtomicFact(atomic_fact) => self.infer_atomic_fact(atomic_fact),
            OrAndChainAtomicFact::AndFact(and_fact) => self.infer_and_fact(and_fact),
            OrAndChainAtomicFact::ChainFact(chain_fact) => self.infer_chain_fact(chain_fact),
            OrAndChainAtomicFact::OrFact(or_fact) => self.infer_or_fact(or_fact),
        }
    }

    fn infer_exist_fact(
        &mut self,
        exist_fact: &ExistFactEnum,
    ) -> Result<InferResult, RuntimeError> {
        let mut out = InferResult::new();
        if exist_fact.is_exist_unique() && exist_fact.params_def_with_type().number_of_params() > 0
        {
            let uniq = self.build_exist_unique_uniqueness_forall_fact(exist_fact)?;
            out.new_infer_result_inside(
                self.store_forall_fact_without_well_defined_verified_and_infer(uniq)?,
            );
        } else if exist_fact.is_not_exist()
            && exist_fact.params_def_with_type().number_of_params() > 0
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

    fn infer_or_fact(&mut self, _or_fact: &OrFact) -> Result<InferResult, RuntimeError> {
        Ok(InferResult::new())
    }

    fn infer_and_fact(&mut self, _and_fact: &AndFact) -> Result<InferResult, RuntimeError> {
        Ok(InferResult::new())
    }

    fn infer_chain_fact(&mut self, chain_fact: &ChainFact) -> Result<InferResult, RuntimeError> {
        let atomic_facts = match chain_fact.facts_with_order_transitive_closure() {
            Ok(v) => v,
            Err(_) => return Ok(InferResult::new()),
        };
        let mut infer_result = InferResult::new();
        for atomic_fact in atomic_facts {
            if let AtomicFact::EqualFact(equal_fact) = atomic_fact {
                infer_result.new_infer_result_inside(self.infer_equal_fact(&equal_fact)?);
            }
        }
        Ok(infer_result)
    }

    // Do not record the whole forall in CLI/JSON `infer_facts`; inner then-clauses are stored as separate facts.
    fn infer_forall_fact(
        &mut self,
        _forall_fact: &ForallFact,
    ) -> Result<InferResult, RuntimeError> {
        Ok(InferResult::new())
    }

    fn infer_forall_fact_with_iff(
        &mut self,
        _forall_fact_with_iff: &ForallFactWithIff,
    ) -> Result<InferResult, RuntimeError> {
        Ok(InferResult::new())
    }
}
