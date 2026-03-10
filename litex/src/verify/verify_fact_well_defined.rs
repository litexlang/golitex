use crate::common::keywords::is_builtin_predicate;
use crate::fact::Fact;
use crate::error::WellDefinedError;
use crate::fact::AtomicFact;
use crate::fact::line_file as atomic_fact_line_file;
use crate::execute::Executor;
use crate::verify::VerifyState;

// well-defined check for fact: 1. predicate is defined 2. all args are well-defined
impl<'a> Executor<'a> {
    pub fn verify_fact_well_defined(&self, fact: &Fact, verify_state: &mut VerifyState) -> Result<(), WellDefinedError> {
        match fact {
            Fact::AtomicFact(atomic_fact) => self.verify_atomic_fact_well_defined(atomic_fact, verify_state).map_err(WellDefinedError::from),
            _ => return Err(WellDefinedError::new("verify_fact_well_defined: NOT IMPLEMENTED YET", vec![], fact.line_file())),
        }
    }

    fn verify_atomic_fact_well_defined(&self, atomic_fact: &AtomicFact, verify_state: &mut VerifyState) -> Result<(), WellDefinedError> {
        // 1. predicate is defined, expected args length is equal to actual args length
        let name_string = atomic_fact.key();
        if is_builtin_predicate(&name_string) {
            let expected_len = atomic_fact.is_builtin_predicate_and_return_defined_args_len();
            let actual_args = atomic_fact.args();
            if actual_args.len() != expected_len {
                return Err(WellDefinedError::new(
                    &format!(
                        "predicate {} expects {} argument(s), but got {}",
                        name_string,
                        expected_len,
                        actual_args.len()
                    ),
                    vec![],
                    atomic_fact_line_file(atomic_fact),
                ));
            }
        } else {
            let predicate_definition = self.runtime_context.get_predicate_definition_by_name(&name_string);
            if predicate_definition.is_none() {
                return Err(WellDefinedError::new(
                    "predicate not defined",
                    vec![],
                    atomic_fact_line_file(atomic_fact),
                ));
            }
            let def = predicate_definition.unwrap();
    
            let expected_len = def.params_def_with_type.len();
            let actual_args = atomic_fact.args();
            if actual_args.len() != expected_len {
                return Err(WellDefinedError::new(
                    &format!(
                        "predicate {} expects {} argument(s), but got {}",
                        name_string,
                        expected_len,
                        actual_args.len()
                    ),
                    vec![],
                    atomic_fact_line_file(atomic_fact),
                ));
            }    

        }

        // 2. all args are well-defined
        for arg in atomic_fact.args() {
            self.verify_obj_well_defined(&arg, verify_state)?;
        }
        
        Ok(())
    }
}

