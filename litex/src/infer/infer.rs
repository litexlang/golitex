use crate::error::ExecError;
use crate::execute::Executor;
use crate::fact::{AndFact, AtomicFact, ChainFact, EqualFact, ExistFact, Fact, ForallFact, ForallFactWithIff, InFact, OrFact};
use crate::obj::{FnSetObj, Obj};

impl<'a> Executor<'a> {
    pub fn infer(&mut self, fact: &Fact) -> Result<(), ExecError> {
        match fact {
            Fact::AtomicFact(atomic_fact) => self.infer_atomic_fact(atomic_fact),
            Fact::ExistFact(exist_fact) => self.infer_exist_fact(exist_fact),
            Fact::OrFact(or_fact) => self.infer_or_fact(or_fact),
            Fact::AndFact(and_fact) => self.infer_and_fact(and_fact),
            Fact::ChainFact(chain_fact) => self.infer_chain_fact(chain_fact),
            Fact::ForallFact(forall_fact) => self.infer_forall_fact(forall_fact),
            Fact::ForallFactWithIff(forall_fact_with_iff) => self.infer_forall_fact_with_iff(forall_fact_with_iff),
        }
    }

    fn infer_atomic_fact(&mut self, _atomic_fact: &AtomicFact) -> Result<(), ExecError> {
        match _atomic_fact {
            AtomicFact::EqualFact(equal_fact) => self.infer_equal_fact(equal_fact),
            AtomicFact::InFact(in_fact) => self.infer_in_fact(in_fact),
            _ => Ok(()),
        }
    }

    fn infer_exist_fact(&mut self, _exist_fact: &ExistFact) -> Result<(), ExecError> {
        Ok(())
    }

    fn infer_or_fact(&mut self, _or_fact: &OrFact) -> Result<(), ExecError> {
        Ok(())
    }

    fn infer_and_fact(&mut self, _and_fact: &AndFact) -> Result<(), ExecError> {
        Ok(())
    }

    fn infer_chain_fact(&mut self, _chain_fact: &ChainFact) -> Result<(), ExecError> {
        Ok(())
    }

    fn infer_forall_fact(&mut self, _forall_fact: &ForallFact) -> Result<(), ExecError> {
        Ok(())
    }

    fn infer_forall_fact_with_iff(
        &mut self,
        _forall_fact_with_iff: &ForallFactWithIff,
    ) -> Result<(), ExecError> {
        Ok(())
    }

    fn infer_equal_fact(&mut self, _equal_fact: &EqualFact) -> Result<(), ExecError> {
        Ok(())
    }

    fn infer_in_fact(&mut self, in_fact: &InFact) -> Result<(), ExecError> {
        match &in_fact.set {
            Obj::FnSetWithDom(fn_set_with_dom) => {
                let is_element_atom = match &in_fact.element {
                    Obj::Identifier(_)
                    | Obj::IdentifierWithMod(_)
                    | Obj::FieldAccess(_)
                    | Obj::FieldAccessWithMod(_) => true,
                    _ => false,
                };

                if !is_element_atom {
                    return Ok(());
                }

                let key = in_fact.element.to_string();
                let fn_set_obj = FnSetObj::FnSetWithDom(fn_set_with_dom.clone());

                let env = self
                    .runtime_context
                    .environments
                    .last_mut()
                    .unwrap();
                env.known_fn_in_fn_set.insert(key, fn_set_obj);

                Ok(())
            }
            Obj::FnSetWithoutDom(fn_set_without_dom) => {
                let is_element_atom = match &in_fact.element {
                    Obj::Identifier(_)
                    | Obj::IdentifierWithMod(_)
                    | Obj::FieldAccess(_)
                    | Obj::FieldAccessWithMod(_) => true,
                    _ => false,
                };

                if !is_element_atom {
                    return Ok(());
                }

                let key = in_fact.element.to_string();
                let fn_set_obj = FnSetObj::FnSetWithoutDom(fn_set_without_dom.clone());

                let env = self
                    .runtime_context
                    .environments
                    .last_mut()
                    .unwrap();
                env.known_fn_in_fn_set.insert(key, fn_set_obj);

                Ok(())
            }
            _ => Ok(()),
        }
    }
}