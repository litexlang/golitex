use super::store_fact_and_infer_result::{
    InferFromStoredFactResult, StoreFactAndInferResult,
};
use crate::new_pipeline::ast::fact::{AtomicFact, Fact};
use crate::new_pipeline::execute::execute_fact_stmt::VerifyFactResult;
use crate::new_pipeline::execution_environment::helper::{
    ast_obj_key, atomic_fact_args_ref, atomic_fact_has_positive_polarity, atomic_fact_id,
    atomic_fact_key,
};
use crate::new_pipeline::runtime::{Runtime, RuntimeError, RuntimeResult, FactId};

impl Runtime {
    // Store the verified fact into the top ExecEnv; infer is still a no-op.
    pub fn store_fact_then_infer(
        &mut self,
        fact: &Fact,
        verify_result: &VerifyFactResult,
    ) -> RuntimeResult<StoreFactAndInferResult> {
        if verify_result.is_unknown() {
            return Err(RuntimeError::Invariant(
                "store_fact_then_infer: refusing to store an unknown verify result".to_string(),
            ));
        }
        let stored_fact_ids = self.store_fact(fact)?;
        let _infer = self.infer_from_stored_facts(&stored_fact_ids)?;
        Ok(StoreFactAndInferResult::from_stored_ids(stored_fact_ids))
    }

    pub fn store_fact(&mut self, fact: &Fact) -> RuntimeResult<Vec<FactId>> {
        match fact {
            Fact::AtomicFact(atomic_fact) => self.store_atomic_fact(atomic_fact),
            Fact::AndFact(_)
            | Fact::ChainFact(_)
            | Fact::OrFact(_)
            | Fact::ExistFact(_)
            | Fact::ForallFact(_)
            | Fact::ForallFactWithIff(_)
            | Fact::NotForall(_) => Err(RuntimeError::Unsupported(
                "store_fact: only AtomicFact store is implemented so far".to_string(),
            )),
        }
    }

    pub fn store_atomic_fact(&mut self, atomic_fact: &AtomicFact) -> RuntimeResult<Vec<FactId>> {
        match atomic_fact {
            AtomicFact::EqualFact(equal_fact) => {
                let fact_id = equal_fact.fact_id;
                let left_key = ast_obj_key(&equal_fact.left);
                let right_key = ast_obj_key(&equal_fact.right);
                let env = self.top_exec_env_mut();
                env.facts
                    .known_equality
                    .store(equal_fact, left_key, right_key);
                env.facts
                    .facts_by_id
                    .insert(fact_id, Fact::AtomicFact(atomic_fact.clone()));
                Ok(vec![fact_id])
            }
            _ => {
                let fact_id = atomic_fact_id(atomic_fact);
                let key = atomic_fact_key(atomic_fact);
                let positive_polarity = atomic_fact_has_positive_polarity(atomic_fact);
                let args = atomic_fact_args_ref(atomic_fact);
                let env = self.top_exec_env_mut();
                match args.as_slice() {
                    [arg0] => {
                        env.facts.known_atomic_except_equality_facts.store_one_arg(
                            key,
                            positive_polarity,
                            ast_obj_key(arg0),
                            atomic_fact.clone(),
                        );
                    }
                    [arg0, arg1] => {
                        env.facts.known_atomic_except_equality_facts.store_two_args(
                            key,
                            positive_polarity,
                            ast_obj_key(arg0),
                            ast_obj_key(arg1),
                            atomic_fact.clone(),
                        );
                    }
                    _ => {
                        env.facts
                            .known_atomic_except_equality_facts
                            .store_other_arg_count(key, positive_polarity, atomic_fact.clone());
                    }
                }
                env.facts
                    .facts_by_id
                    .insert(fact_id, Fact::AtomicFact(atomic_fact.clone()));
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
