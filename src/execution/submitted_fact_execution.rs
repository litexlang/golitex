use crate::error::RuntimeError;
use crate::fact::Fact;
use crate::inference::InferReason;
use crate::result::{StmtResult, SuccessFactStmtResult, SuccessStoreFactResult, VerifyFactResult};
use crate::runtime::Runtime;
use crate::verification::VerifyState;
use std::result::Result;

impl Runtime {
    pub fn execute_submitted_fact(&mut self, fact: &Fact) -> Result<StmtResult, RuntimeError> {
        // WD and truth search may store intermediate facts so later recursive
        // calls in this same verification process can cite them. Those stores
        // are proof-local evidence, not mathematical consequences published
        // by the source statement. Freeze their exact FactIds into the
        // returned Result DAG before discarding the temporary Runtime
        // environment; only reusable object-shape knowledge and the
        // submitted fact itself are stored below.
        let (verification, verification_environment) =
            self.run_in_local_env_and_take(|runtime| {
                let mut verification =
                    runtime.verify_fact_or_error(fact, &VerifyState::initial())?;
                runtime.attach_known_fact_ids_to_verify_fact_result(&mut verification)?;
                Ok::<_, RuntimeError>(verification)
            })?;
        // Object-shape knowledge learned while checking the fact is a
        // mathematical consequence of the successful verification (for
        // example a template instance's registered set-builder definition).
        // Preserve that knowledge, but deliberately drop the child fact
        // table and inference cache: those are process-local proof stores and
        // are already frozen into `verification` where needed.
        eprintln!("DBG child object effects symbols={:?} objects={:?} tuple={} cart={} fn={} sb={}", verification_environment.definitions.symbols.iter().map(|(name, definition)| (name.clone(), definition.role())).collect::<Vec<_>>(), verification_environment.objects.knowledge_by_object.keys().collect::<Vec<_>>(), verification_environment.objects.tuple_equality_count(), verification_environment.objects.cart_equality_count(), verification_environment.objects.function_set_count(), verification_environment.objects.set_builder_equality_count());
        self.top_level_env()
            .merge_committed_object_effects(verification_environment)?;
        let VerifyFactResult::Verified(verification) = verification else {
            unreachable!("verify_fact_or_error cannot return an unknown fact")
        };
        let infer_result = self.store_without_well_defined_verification_and_infer(fact.clone())?;
        let mut store = SuccessStoreFactResult::new(fact.clone(), infer_result);
        store.fact_id = self.known_fact_id_for_fact(fact)?;
        Ok(SuccessFactStmtResult::verified(verification, store).into())
    }

    pub fn execute_fact_with_trust(&mut self, fact: &Fact) -> Result<StmtResult, RuntimeError> {
        let infer_result = self.store_fact_with_trust_and_infer_with_reason(
            fact.clone(),
            InferReason::StatementWithVerification,
        )?;

        Ok(SuccessFactStmtResult::trusted(fact.clone(), infer_result).into())
    }
}
