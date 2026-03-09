use crate::verifier::Verifier;
use crate::atom::Identifier;
use crate::obj::FnObj;
use crate::keywords::is_builtin_predicate;
use crate::fact::Fact;
use crate::errors::WellDefinedError;
use crate::atomic_fact::AtomicFact;
use crate::atomic_fact::line_file as atomic_fact_line_file;
use crate::obj::Obj;

// well-defined check for fact
impl<'a> Verifier<'a> {
    pub fn verify_fact_well_defined(&self, fact: &Fact) -> Result<bool, WellDefinedError> {
        match fact {
            Fact::AtomicFact(atomic_fact) => self.verify_atomic_fact_well_defined(atomic_fact),
            _ => Err(WellDefinedError::new("verify_fact_well_defined: NOT IMPLEMENTED YET", vec![], fact.line_file())),
        }
    }

    pub fn verify_atomic_fact_well_defined(&self, atomic_fact: &AtomicFact) -> Result<bool, WellDefinedError> {
        // 1. predicate 定义过了：先看 name 是不是 builtin 之一或从环境里拿到的定义
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
            return Ok(true);
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
    
            // 2. predicate 定义时的参数量等于现在传入的量
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

        // 3. 所有的 arg 都是 well-defined 的
        for arg in atomic_fact.args() {
            self.verify_obj_well_defined(&arg)?;
        }
            
        
        Ok(true)
    }
}

// well-defined check for obj
impl<'a> Verifier<'a> {
    pub fn verify_obj_well_defined(&self, _obj: &Obj) -> Result<bool, WellDefinedError> {
        match _obj {
            Obj::Identifier(identifier) => self.verify_identifier_well_defined(identifier),
            Obj::FnObj(_obj) => self.verify_fn_obj_well_defined(_obj),
            _ => Err(WellDefinedError::new("verify_obj_well_defined: NOT IMPLEMENTED YET", vec![], None))
        }
    }

    pub fn verify_identifier_well_defined(&self, identifier: &Identifier) -> Result<bool, WellDefinedError> {
        Err(WellDefinedError::new("verify_identifier_well_defined: NOT IMPLEMENTED YET", vec![], None))
    }

    pub fn verify_fn_obj_well_defined(&self, fn_obj: &FnObj) -> Result<bool, WellDefinedError> {
        Err(WellDefinedError::new("verify_fn_obj_well_defined: NOT IMPLEMENTED YET", vec![], None))
    }
}