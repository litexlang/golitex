use crate::fact::InFact;
use crate::obj::{Add, FnObj, Identifier, Mul, Obj, RObj, Sub};
use crate::common::keywords::is_builtin_predicate;
use crate::fact::Fact;
use crate::error::WellDefinedError;
use crate::fact::AtomicFact;
use crate::fact::line_file as atomic_fact_line_file;
use crate::execute::Executor;
use crate::verify::VerifyState;

// well-defined check for fact
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

// well-defined check for obj
impl<'a> Executor<'a> {
    fn verify_obj_well_defined(&self, obj: &Obj, verify_state: &mut VerifyState) -> Result<(), WellDefinedError> {
        match obj {
            Obj::Identifier(identifier) => self.verify_identifier_well_defined(identifier, verify_state),
            Obj::FnObj(fn_obj) => self.verify_fn_obj_well_defined(fn_obj, verify_state),
            Obj::Number(_) => Ok(()),
            Obj::Add(add) => self.verify_add_well_defined(add, verify_state),
            Obj::Sub(sub) => self.verify_sub_well_defined(sub, verify_state),
            Obj::Mul(mul) => self.verify_mul_well_defined(mul, verify_state),
            _ => Err(WellDefinedError::new("verify_obj_well_defined: NOT IMPLEMENTED YET", vec![], None)),
        }
    }

    fn verify_identifier_well_defined(&self, identifier: &Identifier, _verify_state: &mut VerifyState) -> Result<(), WellDefinedError> {
        if self.runtime_context.is_identifier_defined(identifier) {
            Ok(())
        } else {
            Err(WellDefinedError::new("identifier not defined", vec![], None))
        }
    }

    fn verify_fn_obj_well_defined(&self, fn_obj: &FnObj, _verify_state: &mut VerifyState) -> Result<(), WellDefinedError> {
        let _ = fn_obj;
        Err(WellDefinedError::new("verify_fn_obj_well_defined: NOT IMPLEMENTED YET", vec![], None))
    }

    fn require_obj_is_real_number(&self, obj: &Obj, verify_state: &mut VerifyState) -> Result<(), WellDefinedError> {
        let r_obj = Obj::RObj(RObj::new());
        let in_fact = InFact::new(obj.clone(), r_obj, None);
        let atomic_fact = AtomicFact::InFact(in_fact);
        self.verify_atomic_fact(&atomic_fact, verify_state)?;
        Ok(())
    }

    fn verify_add_well_defined(&self, add: &Add, verify_state: &mut VerifyState) -> Result<(), WellDefinedError> {
        self.verify_obj_well_defined(&add.left, verify_state)?;
        self.verify_obj_well_defined(&add.right, verify_state)?;
        self.require_obj_is_real_number(&add.left, verify_state)?;
        self.require_obj_is_real_number(&add.right, verify_state)?;
        Ok(())
    }

    fn verify_sub_well_defined(&self, sub: &Sub, verify_state: &mut VerifyState) -> Result<(), WellDefinedError> {
        self.verify_obj_well_defined(&sub.left, verify_state)?;
        self.verify_obj_well_defined(&sub.right, verify_state)?;
        self.require_obj_is_real_number(&sub.left, verify_state)?;
        self.require_obj_is_real_number(&sub.right, verify_state)?;
        Ok(())
    }

    fn verify_mul_well_defined(&self, mul: &Mul, verify_state: &mut VerifyState) -> Result<(), WellDefinedError> {
        self.verify_obj_well_defined(&mul.left, verify_state)?;
        self.verify_obj_well_defined(&mul.right, verify_state)?;
        self.require_obj_is_real_number(&mul.left, verify_state)?;
        self.require_obj_is_real_number(&mul.right, verify_state)?;
        Ok(())
    }
}
