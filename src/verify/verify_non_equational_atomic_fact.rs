use crate::prelude::*;

impl Runtime {
    pub fn verify_non_equational_atomic_fact(
        &mut self,
        atomic_fact: &AtomicFact,
        verify_state: &VerifyState,
        post_process: bool,
    ) -> Result<StmtResult, RuntimeError> {
        let mut result =
            self.verify_non_equational_atomic_fact_with_builtin_rules(atomic_fact, verify_state)?;
        if result.is_true() {
            return Ok(result);
        }

        result = self.verify_non_equational_atomic_fact_with_known_atomic_facts(atomic_fact)?;
        if result.is_true() {
            return Ok(result);
        }

        if verify_state.is_round_0() {
            let verify_state_add_one_round = verify_state.new_state_with_round_increased();

            if let Some(verified_by_definition) =
                self.verify_atomic_fact_using_builtin_or_prop_definition(atomic_fact, verify_state)?
            {
                return Ok(verified_by_definition);
            }

            result = self
                .verify_atomic_fact_with_known_forall(atomic_fact, &verify_state_add_one_round)?;
            if result.is_true() {
                return Ok(result);
            }
        }

        if post_process {
            result =
                self.post_process_non_equational_atomic_fact(atomic_fact, verify_state, result)?;
            if result.is_true() {
                return Ok(result);
            }
        }

        Ok((StmtUnknown::new()).into())
    }

    pub fn verify_fact(
        &mut self,
        fact: &Fact,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        match fact {
            Fact::AtomicFact(atomic_fact) => self.verify_atomic_fact(atomic_fact, verify_state),
            Fact::AndFact(and_fact) => self.verify_and_fact(and_fact, verify_state),
            Fact::ChainFact(chain_fact) => self.verify_chain_fact(chain_fact, verify_state),
            Fact::ForallFact(forall_fact) => self.verify_forall_fact(forall_fact, verify_state),
            Fact::ForallFactWithIff(forall_iff) => {
                self.verify_forall_fact_with_iff(forall_iff, verify_state)
            }
            Fact::NotForall(not_forall) => self.verify_not_forall_fact(not_forall, verify_state),
            Fact::ExistFact(exist_fact) => self.verify_exist_fact(exist_fact, verify_state),
            Fact::OrFact(or_fact) => self.verify_or_fact(or_fact, verify_state),
        }
    }

    // If direct verification failed, try the order-dual (e.g. a >= b via b <= a), then commutative props.
    fn post_process_non_equational_atomic_fact(
        &mut self,
        atomic_fact: &AtomicFact,
        verify_state: &VerifyState,
        result: StmtResult,
    ) -> Result<StmtResult, RuntimeError> {
        let result = self.builtin_post_process_non_equational_atomic_fact(
            atomic_fact,
            verify_state,
            result,
        )?;
        if result.is_true() {
            return Ok(result);
        }
        self.use_known_commutative_prop(atomic_fact, verify_state, result)
    }

    fn builtin_post_process_non_equational_atomic_fact(
        &mut self,
        atomic_fact: &AtomicFact,
        verify_state: &VerifyState,
        result: StmtResult,
    ) -> Result<StmtResult, RuntimeError> {
        let Some(transposed_fact) = atomic_fact.transposed_binary_order_equivalent() else {
            return Ok(result);
        };
        let transposed_result =
            self.verify_non_equational_atomic_fact(&transposed_fact, verify_state, false)?;
        Self::wrap_post_process_alternate_fact_result(atomic_fact, transposed_result, result)
    }

    fn use_known_commutative_prop(
        &mut self,
        atomic_fact: &AtomicFact,
        verify_state: &VerifyState,
        result: StmtResult,
    ) -> Result<StmtResult, RuntimeError> {
        let prop_name = match atomic_fact {
            AtomicFact::NormalAtomicFact(f) if f.body.len() == 2 => f.predicate.to_string(),
            _ => return Ok(result),
        };
        if !self.is_commutative_prop_name_known(&prop_name) {
            return Ok(result);
        }
        let Some(swapped_fact) = atomic_fact.commutative_swapped_binary_args() else {
            return Ok(result);
        };
        let swapped_result =
            self.verify_non_equational_atomic_fact(&swapped_fact, verify_state, false)?;
        Self::wrap_post_process_alternate_fact_result(atomic_fact, swapped_result, result)
    }

    fn wrap_post_process_alternate_fact_result(
        original: &AtomicFact,
        alternate_result: StmtResult,
        fallback: StmtResult,
    ) -> Result<StmtResult, RuntimeError> {
        match alternate_result {
            StmtResult::FactualStmtSuccess(inner_success) => {
                let FactualStmtSuccess {
                    verified_by,
                    infers: _,
                    stmt: _,
                } = inner_success;
                Ok(FactualStmtSuccess::new_with_verified_by_known_fact(
                    original.clone().into(),
                    verified_by,
                    Vec::new(),
                )
                .into())
            }
            other if other.is_true() => Ok(other),
            _ => Ok(fallback),
        }
    }
}
