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

            result = self.verify_non_equational_atomic_fact_with_strategy(
                atomic_fact,
                &verify_state_add_one_round,
            )?;
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

    // If direct verification failed, try order-dual, then registered user-defined prop properties.
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
        let result = self.use_known_reflexive_prop(atomic_fact, result)?;
        if result.is_true() {
            return Ok(result);
        }
        self.use_known_symmetric_prop(atomic_fact, verify_state, result)
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

    fn use_known_reflexive_prop(
        &mut self,
        atomic_fact: &AtomicFact,
        result: StmtResult,
    ) -> Result<StmtResult, RuntimeError> {
        let AtomicFact::NormalAtomicFact(f) = atomic_fact else {
            return Ok(result);
        };
        if f.body.len() != 2 {
            return Ok(result);
        }
        if f.body[0].to_string() != f.body[1].to_string() {
            return Ok(result);
        }
        let prop_name = f.predicate.to_string();
        for env in self.iter_environments_from_top() {
            if env.known_reflexive_props.contains_key(&prop_name) {
                return Ok(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        atomic_fact.clone().into(),
                        "registered reflexive prop".to_string(),
                        Vec::new(),
                    )
                    .into(),
                );
            }
        }
        Ok(result)
    }

    fn use_known_symmetric_prop(
        &mut self,
        atomic_fact: &AtomicFact,
        verify_state: &VerifyState,
        result: StmtResult,
    ) -> Result<StmtResult, RuntimeError> {
        let AtomicFact::NormalAtomicFact(f) = atomic_fact else {
            return Ok(result);
        };
        if f.body.len() < 2 {
            return Ok(result);
        }
        let prop_name = f.predicate.to_string();

        let mut permutations: Vec<Vec<usize>> = Vec::new();
        for env in self.iter_environments_from_top() {
            if let Some(perms) = env.known_symmetric_props.get(&prop_name) {
                for g in perms {
                    if g.len() == f.body.len() {
                        permutations.push(g.clone());
                    }
                }
            }
        }

        for gather in permutations {
            let Some(alt) = atomic_fact.symmetric_reordered_args(&gather) else {
                continue;
            };
            let alt_result = self.verify_non_equational_atomic_fact(&alt, verify_state, false)?;
            if alt_result.is_true() {
                return Self::wrap_post_process_alternate_fact_result(
                    atomic_fact,
                    alt_result,
                    result,
                );
            }
        }

        Ok(result)
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
