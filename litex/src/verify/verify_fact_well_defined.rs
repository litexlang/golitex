use crate::common::keywords::is_builtin_predicate;
use crate::error::{RuntimeError, WellDefinedError};
use crate::execute::Runtime;
use crate::fact::line_file as atomic_fact_line_file;
use crate::fact::AtomicFact;
use crate::fact::{
    AndChainAtomicFact, AndFact, ChainFact, EqualFact, ExistFact, ExistOrAndChainAtomicFact, Fact,
    ForallFact, ForallFactWithIff, OrAndChainAtomicFact, OrFact,
};
use crate::stmt::parameter_def::ParamDefWithParamType;
use crate::stmt::tooling_stmt::DoNothingStmt;
use crate::stmt::Stmt;
use crate::verify::VerifyState;

// well-defined check for fact: 1. predicate is defined 2. all args are well-defined
// store verified related facts during the verification process, e.g. when verifying f(a)(b) is well-defined, we store f(a) in the set where f returns, and store f(a)(b) in the set where f(a) returns
impl<'a> Runtime<'a> {
    pub fn verify_fact_well_defined(
        &mut self,
        fact: &Fact,
        verify_state: &VerifyState,
    ) -> Result<(), WellDefinedError> {
        let result = match fact {
            Fact::AtomicFact(atomic_fact) => self
                .verify_atomic_fact_well_defined(atomic_fact, verify_state)
                .map_err(WellDefinedError::from),
            Fact::AndFact(and_fact) => self
                .verify_and_fact_well_defined(and_fact, verify_state)
                .map_err(WellDefinedError::from),
            Fact::ChainFact(chain_fact) => self
                .verify_chain_fact_well_defined(chain_fact, verify_state)
                .map_err(WellDefinedError::from),
            Fact::OrFact(or_fact) => self
                .verify_or_fact_well_defined(or_fact, verify_state)
                .map_err(WellDefinedError::from),
            Fact::ExistFact(exist_fact) => self
                .verify_exist_fact_well_defined(exist_fact, verify_state)
                .map_err(WellDefinedError::from),
            Fact::ForallFact(forall_fact) => self
                .verify_forall_fact_well_defined(forall_fact, verify_state)
                .map_err(WellDefinedError::from),
            Fact::ForallFactWithIff(forall_fact_with_iff) => self
                .verify_forall_fact_with_iff_well_defined(forall_fact_with_iff, verify_state)
                .map_err(WellDefinedError::from),
        };
        result
    }

    pub fn verify_atomic_fact_well_defined(
        &mut self,
        atomic_fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<(), WellDefinedError> {
        match atomic_fact {
            AtomicFact::EqualFact(equal_fact) => {
                self.verify_equal_fact_well_defined(equal_fact, verify_state)
            }
            _ => self
                .verify_non_equational_atomic_fact_well_defined(atomic_fact, verify_state)
                .map_err(WellDefinedError::from),
        }
    }

    fn verify_equal_fact_well_defined(
        &mut self,
        equal_fact: &EqualFact,
        verify_state: &VerifyState,
    ) -> Result<(), WellDefinedError> {
        self.verify_obj_well_defined_and_store_cache(&equal_fact.left, verify_state)?;
        self.verify_obj_well_defined_and_store_cache(&equal_fact.right, verify_state)?;
        Ok(())
    }

    fn verify_non_equational_atomic_fact_well_defined(
        &mut self,
        atomic_fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<(), WellDefinedError> {
        // 1. predicate is defined, expected args length is equal to actual args length
        let name_string = atomic_fact.key();
        if is_builtin_predicate(&name_string) {
            let expected_len = atomic_fact.is_builtin_predicate_and_return_expected_args_len();
            let actual_args = atomic_fact.args();
            if actual_args.len() != expected_len {
                return Err(WellDefinedError::new(
                    format!(
                        "fact `{}` expects {} argument(s), but got {}",
                        name_string,
                        expected_len,
                        actual_args.len()
                    ),
                    None,
                    atomic_fact_line_file(atomic_fact),
                ));
            }
        } else {
            let expected_len = if let Some(predicate_definition) = self
                .runtime_context
                .get_predicate_with_meaning_definition_by_name(&name_string)
            {
                ParamDefWithParamType::number_of_params(&predicate_definition.params_def_with_type)
            } else if let Some(predicate_without_meaning_definition) = self
                .runtime_context
                .get_predicate_without_meaning_definition_by_name(&name_string)
            {
                predicate_without_meaning_definition.params.len()
            } else {
                return Err(WellDefinedError::new(
                    format!("fact `{}` not defined", name_string),
                    None,
                    atomic_fact_line_file(atomic_fact),
                ));
            };

            let actual_args = atomic_fact.args();
            if actual_args.len() != expected_len {
                return Err(WellDefinedError::new(
                    format!(
                        "fact `{}` expects {} argument(s), but got {}",
                        name_string,
                        expected_len,
                        actual_args.len()
                    ),
                    None,
                    atomic_fact_line_file(atomic_fact),
                ));
            }
        }

        // 2. all args are well-defined
        for arg in atomic_fact.args() {
            self.verify_obj_well_defined_and_store_cache(&arg, verify_state)?;
        }

        Ok(())
    }

    pub(crate) fn verify_and_fact_well_defined(
        &mut self,
        and_fact: &AndFact,
        verify_state: &VerifyState,
    ) -> Result<(), WellDefinedError> {
        for fact in and_fact.facts.iter() {
            self.verify_atomic_fact_well_defined(fact, verify_state)?;
        }
        Ok(())
    }

    pub(crate) fn verify_chain_fact_well_defined(
        &mut self,
        chain_fact: &ChainFact,
        verify_state: &VerifyState,
    ) -> Result<(), WellDefinedError> {
        let facts = chain_fact.facts()?;
        for fact in facts.iter() {
            self.verify_atomic_fact_well_defined(fact, verify_state)?;
        }
        Ok(())
    }

    pub(crate) fn verify_or_fact_well_defined(
        &mut self,
        or_fact: &OrFact,
        verify_state: &VerifyState,
    ) -> Result<(), WellDefinedError> {
        for fact in or_fact.facts.iter() {
            self.verify_and_chain_atomic_fact_well_defined(fact, verify_state)?;
        }
        Ok(())
    }

    fn verify_and_chain_atomic_fact_well_defined(
        &mut self,
        fact: &AndChainAtomicFact,
        verify_state: &VerifyState,
    ) -> Result<(), WellDefinedError> {
        match fact {
            AndChainAtomicFact::AtomicFact(a) => {
                self.verify_atomic_fact_well_defined(a, verify_state)?
            }
            AndChainAtomicFact::AndFact(a) => self.verify_and_fact_well_defined(a, verify_state)?,
            AndChainAtomicFact::ChainFact(c) => {
                self.verify_chain_fact_well_defined(c, verify_state)?
            }
        }
        Ok(())
    }

    pub(crate) fn verify_exist_fact_well_defined(
        &mut self,
        exist_fact: &ExistFact,
        verify_state: &VerifyState,
    ) -> Result<(), WellDefinedError> {
        self.runtime_context.push_env();
        let result = self.verify_exist_fact_well_defined_body(&exist_fact, verify_state);
        self.runtime_context.pop_env();
        result
    }

    fn verify_exist_fact_well_defined_body(
        &mut self,
        exist_fact: &ExistFact,
        verify_state: &VerifyState,
    ) -> Result<(), WellDefinedError> {
        for param_def in exist_fact.params_def_with_type().iter() {
            let result = self.define_params_with_type(
                std::slice::from_ref(param_def),
                false,
                Stmt::DoNothingStmt(DoNothingStmt::new(exist_fact.line_file())),
            );
            if let Err(e) = result {
                return Err(WellDefinedError::new(
                    format!(
                        "failed to define parameters in {}:\n{}",
                        exist_fact,
                        e.body_string()
                    ),
                    None,
                    exist_fact.line_file(),
                ));
            }
        }

        for fact in exist_fact.facts() {
            self.verify_or_and_chain_atomic_fact_well_defined(fact, verify_state)?;
        }
        Ok(())
    }

    pub(crate) fn verify_forall_fact_well_defined(
        &mut self,
        forall_fact: &ForallFact,
        verify_state: &VerifyState,
    ) -> Result<(), WellDefinedError> {
        self.runtime_context.push_env();
        let result = self.verify_forall_fact_well_defined_body(&forall_fact, verify_state);
        self.runtime_context.pop_env();
        result
    }

    fn verify_forall_fact_well_defined_body(
        &mut self,
        forall_fact: &ForallFact,
        verify_state: &VerifyState,
    ) -> Result<(), WellDefinedError> {
        for param_def in forall_fact.params_def_with_type.iter() {
            if let Err(e) = self.define_params_with_type(
                std::slice::from_ref(param_def),
                false,
                Stmt::DoNothingStmt(DoNothingStmt::new(forall_fact.line_file)),
            ) {
                return Err(WellDefinedError::new(
                    format!(
                        "failed to define parameters in {}:\n{}",
                        forall_fact,
                        e.body_string()
                    ),
                    None,
                    forall_fact.line_file,
                ));
            }
        }

        for fact in forall_fact.dom_facts.iter() {
            if let Err(exec_stmt_error) = self
                .verify_exist_or_and_chain_atomic_fact_well_defined_and_store_and_infer(
                    fact,
                    verify_state,
                )
            {
                return Err(WellDefinedError::new(
                    format!(
                        "failed to store fact in environment: {}",
                        exec_stmt_error.body_string()
                    ),
                    Some(RuntimeError::ExecStmtError(exec_stmt_error)),
                    fact.line_file(),
                ));
            }
        }
        for fact in forall_fact.then_facts.iter() {
            if let Err(exec_stmt_error) = self
                .verify_exist_or_and_chain_atomic_fact_well_defined_and_store_and_infer(
                    fact,
                    verify_state,
                )
            {
                return Err(WellDefinedError::new(
                    format!(
                        "failed to store fact in environment: {}",
                        exec_stmt_error.body_string()
                    ),
                    Some(RuntimeError::ExecStmtError(exec_stmt_error)),
                    fact.line_file(),
                ));
            }
        }
        Ok(())
    }

    pub fn verify_or_and_chain_atomic_fact_well_defined(
        &mut self,
        fact: &OrAndChainAtomicFact,
        verify_state: &VerifyState,
    ) -> Result<(), WellDefinedError> {
        match fact {
            OrAndChainAtomicFact::AtomicFact(a) => {
                self.verify_atomic_fact_well_defined(a, verify_state)?
            }
            OrAndChainAtomicFact::AndFact(a) => {
                self.verify_and_fact_well_defined(a, verify_state)?
            }
            OrAndChainAtomicFact::ChainFact(c) => {
                self.verify_chain_fact_well_defined(c, verify_state)?
            }
            OrAndChainAtomicFact::OrFact(o) => self.verify_or_fact_well_defined(o, verify_state)?,
        }
        Ok(())
    }

    pub(crate) fn verify_exist_or_and_chain_atomic_fact_well_defined(
        &mut self,
        fact: &ExistOrAndChainAtomicFact,
        verify_state: &VerifyState,
    ) -> Result<(), WellDefinedError> {
        match fact {
            ExistOrAndChainAtomicFact::AtomicFact(a) => {
                self.verify_atomic_fact_well_defined(a, verify_state)?
            }
            ExistOrAndChainAtomicFact::AndFact(a) => {
                self.verify_and_fact_well_defined(a, verify_state)?
            }
            ExistOrAndChainAtomicFact::ChainFact(c) => {
                self.verify_chain_fact_well_defined(c, verify_state)?
            }
            ExistOrAndChainAtomicFact::OrFact(o) => {
                self.verify_or_fact_well_defined(o, verify_state)?
            }
            ExistOrAndChainAtomicFact::ExistFact(e) => {
                self.verify_exist_fact_well_defined(e, verify_state)?
            }
        }
        Ok(())
    }

    pub(crate) fn verify_forall_fact_with_iff_well_defined(
        &mut self,
        forall_fact_with_iff: &ForallFactWithIff,
        verify_state: &VerifyState,
    ) -> Result<(), WellDefinedError> {
        self.runtime_context.push_env();
        let result =
            self.verify_forall_fact_with_iff_well_defined_body(forall_fact_with_iff, verify_state);
        self.runtime_context.pop_env();
        result
    }

    fn verify_forall_fact_with_iff_well_defined_body(
        &mut self,
        forall_fact_with_iff: &ForallFactWithIff,
        verify_state: &VerifyState,
    ) -> Result<(), WellDefinedError> {
        self.verify_forall_fact_well_defined_body(&forall_fact_with_iff.forall_fact, verify_state)?;
        for fact in forall_fact_with_iff.iff_facts.iter() {
            self.verify_exist_or_and_chain_atomic_fact_well_defined(fact, verify_state)?;
        }
        Ok(())
    }
}
