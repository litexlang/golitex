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

    fn infer_exist_fact(&mut self, _exist_fact: &ExistFact) -> Result<InferResult, RuntimeError> {
        Ok(InferResult::new())
    }

    fn infer_or_fact(&mut self, _or_fact: &OrFact) -> Result<InferResult, RuntimeError> {
        Ok(InferResult::new())
    }

    fn infer_and_fact(&mut self, _and_fact: &AndFact) -> Result<InferResult, RuntimeError> {
        Ok(InferResult::new())
    }

    fn infer_chain_fact(&mut self, _chain_fact: &ChainFact) -> Result<InferResult, RuntimeError> {
        Ok(InferResult::new())
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
