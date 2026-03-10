use crate::obj::{Obj};
use crate::error::WellDefinedError;
use crate::verify::VerifyState;
use crate::fact::AtomicFact;
use crate::fact::InFact;
use crate::obj::{Add, FnObj, Identifier, Mul, RObj, Sub};
use crate::execute::Executor;

// well-defined check for obj
impl<'a> Executor<'a> {
    pub fn verify_obj_well_defined(&self, obj: &Obj, verify_state: &mut VerifyState) -> Result<(), WellDefinedError> {
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
