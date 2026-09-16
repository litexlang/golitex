use super::store_fact_and_infer_result::{InferFromStoredFactResult, StoreFactAndInferResult};
use crate::new_pipeline::ast::fact::{AtomicFact, Fact};
use crate::new_pipeline::exec_env::helper::{
    atomic_fact_args_ref, atomic_fact_has_positive_polarity,
};
use crate::new_pipeline::runtime::{FactId, Runtime, RuntimeResult};

impl Runtime {
    // Store the verified fact into the top ExecEnv; infer is still a no-op.
    pub fn store_fact_and_infer(&mut self, fact: &Fact) -> RuntimeResult<StoreFactAndInferResult> {
        let stored_fact_ids = self.store_fact(fact)?;
        let _infer = self.infer_from_stored_facts(&stored_fact_ids)?;
        Ok(StoreFactAndInferResult::from_stored_ids(stored_fact_ids))
    }

    // Record the closed fact by FactId; atomics also update equality /
    // atomic-except-equality side indexes.
    pub fn store_fact(&mut self, fact: &Fact) -> RuntimeResult<Vec<FactId>> {
        match fact {
            Fact::AtomicFact(atomic_fact) => self.store_atomic_fact(atomic_fact),
            Fact::AndFact(_)
            | Fact::ChainFact(_)
            | Fact::OrFact(_)
            | Fact::ExistFact(_)
            | Fact::ForallFact(_)
            | Fact::ForallFactWithIff(_)
            | Fact::NotForall(_) => {
                let fact_id = fact.fact_id();
                self.top_exec_env_mut()
                    .facts
                    .record_fact(fact_id, fact.clone());
                Ok(vec![fact_id])
            }
        }
    }

    pub fn store_atomic_fact(&mut self, atomic_fact: &AtomicFact) -> RuntimeResult<Vec<FactId>> {
        match atomic_fact {
            AtomicFact::EqualFact(equal_fact) => {
                let fact_id = equal_fact.fact_id;
                let env = self.top_exec_env_mut();
                env.facts.known_equality.store(equal_fact);
                env.facts.record_atomic_fact(fact_id, atomic_fact.clone());
                Ok(vec![fact_id])
            }
            _ => {
                let fact_id = atomic_fact.fact_id();
                let key = atomic_fact.prop_name();
                let positive_polarity = atomic_fact_has_positive_polarity(atomic_fact);
                let args = atomic_fact_args_ref(atomic_fact);
                let env = self.top_exec_env_mut();
                match args.as_slice() {
                    [arg0] => {
                        env.facts.known_atomic_except_equality_facts.store_one_arg(
                            key,
                            positive_polarity,
                            arg0.ir(),
                            atomic_fact.clone(),
                        );
                    }
                    [arg0, arg1] => {
                        env.facts.known_atomic_except_equality_facts.store_two_args(
                            key,
                            positive_polarity,
                            arg0.ir(),
                            arg1.ir(),
                            atomic_fact.clone(),
                        );
                    }
                    _ => {
                        env.facts
                            .known_atomic_except_equality_facts
                            .store_other_arg_count(key, positive_polarity, atomic_fact.clone());
                    }
                }
                env.facts.record_atomic_fact(fact_id, atomic_fact.clone());
                Ok(vec![fact_id])
            }
        }
    }

    fn infer_from_stored_facts(
        &mut self,
        _stored_fact_ids: &[FactId],
    ) -> RuntimeResult<InferFromStoredFactResult> {
        Ok(InferFromStoredFactResult::empty())
    }
}
