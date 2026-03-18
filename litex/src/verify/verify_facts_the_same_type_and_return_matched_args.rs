use crate::Executor;
use crate::error::VerifyError;
use crate::fact::{ExistOrAndChainAtomicFact, OrAndChainAtomicFact, ChainFact, AndChainAtomicFact, OrFact, AndFact, ExistFact, AtomicFact};
use crate::obj::Obj;

impl<'a> Executor<'a> {
    pub fn _verify_exist_or_and_chain_atomic_facts_the_same_type_and_return_matched_args(&mut self, fact: &ExistOrAndChainAtomicFact, other: &ExistOrAndChainAtomicFact) -> Result<Option<Vec<(Obj, Obj)>>, VerifyError> {
        match fact {
            ExistOrAndChainAtomicFact::ChainFact(f) => {
                match other {
                    ExistOrAndChainAtomicFact::ChainFact(other) => self._verify_chain_fact_the_same_type_and_return_matched_args(f, other),
                    _ => Ok(None)
                }
            },
            ExistOrAndChainAtomicFact::AndFact(f) => {
                match other {
                    ExistOrAndChainAtomicFact::AndFact(other) => self._verify_and_fact_the_same_type_and_return_matched_args(f, other),
                    _ => Ok(None)
                }
            },
            ExistOrAndChainAtomicFact::OrFact(f) => {
                match other {
                    ExistOrAndChainAtomicFact::OrFact(other) => self._verify_or_fact_the_same_type_and_return_matched_args(f, other),
                    _ => Ok(None)
                }
            },
            ExistOrAndChainAtomicFact::ExistFact(f) => {
                match other {
                    ExistOrAndChainAtomicFact::ExistFact(other) => self._verify_exist_fact_the_same_type_and_return_matched_args(f, other),
                    _ => Ok(None)
                }
            },
            ExistOrAndChainAtomicFact::AtomicFact(f) => {
                match other {
                    ExistOrAndChainAtomicFact::AtomicFact(other) => self._verify_atomic_fact_the_same_type_and_return_matched_args(f, other),
                    _ => Ok(None)
                }
            },
        }
    }

    pub fn _verify_or_and_chain_atomic_facts_the_same_type_and_return_matched_args(&mut self, fact: &OrAndChainAtomicFact, other: &OrAndChainAtomicFact) -> Result<Option<Vec<(Obj, Obj)>>, VerifyError> {
        match fact {
            OrAndChainAtomicFact::AndFact(f) => {
                match other {
                    OrAndChainAtomicFact::AndFact(other) => self._verify_and_fact_the_same_type_and_return_matched_args(f, other),
                    _ => Ok(None)
                }
            },
            OrAndChainAtomicFact::OrFact(f) => {
                match other {
                    OrAndChainAtomicFact::OrFact(other) => self._verify_or_fact_the_same_type_and_return_matched_args(f, other),
                    _ => Ok(None)
                }
            },
            OrAndChainAtomicFact::AtomicFact(f) => {
                match other {
                    OrAndChainAtomicFact::AtomicFact(other) => self._verify_atomic_fact_the_same_type_and_return_matched_args(f, other),
                    _ => Ok(None)
                }
            },
            OrAndChainAtomicFact::ChainFact(f) => {
                match other {
                    OrAndChainAtomicFact::ChainFact(other) => self._verify_chain_fact_the_same_type_and_return_matched_args(f, other),
                    _ => Ok(None)
                }
            },
        }
    }

    pub fn _verify_and_chain_atomic_facts_the_same_type_and_return_matched_args(&mut self, fact: &AndChainAtomicFact, other: &AndChainAtomicFact) -> Result<Option<Vec<(Obj, Obj)>>, VerifyError> {
        match fact {
            AndChainAtomicFact::AndFact(f) => {
                match other {
                    AndChainAtomicFact::AndFact(other) => self._verify_and_fact_the_same_type_and_return_matched_args(f, other),
                    _ => Ok(None)
                }
            },
            AndChainAtomicFact::AtomicFact(f) => {
                match other {
                    AndChainAtomicFact::AtomicFact(other) => self._verify_atomic_fact_the_same_type_and_return_matched_args(f, other),
                    _ => Ok(None)
                }
            },
            AndChainAtomicFact::ChainFact(f) => {
                match other {
                    AndChainAtomicFact::ChainFact(other) => self._verify_chain_fact_the_same_type_and_return_matched_args(f, other),
                    _ => Ok(None)
                }
            },
        }
    }

    pub fn _verify_chain_fact_the_same_type_and_return_matched_args(&mut self, fact: &ChainFact, other: &ChainFact) -> Result<Option<Vec<(Obj, Obj)>>, VerifyError> {
        if fact.prop_names.len() != other.prop_names.len() {
            return Ok(None);
        }
        if fact.objs.len() != other.objs.len() {
            return Ok(None);
        }

        for (fact_prop_name, other_prop_name) in fact.prop_names.iter().zip(other.prop_names.iter()) {
            if fact_prop_name.to_string() != other_prop_name.to_string() {
                return Ok(None);
            }
        }

        let mut matched_args: Vec<(Obj, Obj)> = Vec::new();
        for (fact_obj, other_obj) in fact.objs.iter().zip(other.objs.iter()) {
            matched_args.push((fact_obj.clone(), other_obj.clone()));
        }

        Ok(Some(matched_args))
    }

    pub fn _verify_or_fact_the_same_type_and_return_matched_args(&mut self, fact: &OrFact, other: &OrFact) -> Result<Option<Vec<(Obj, Obj)>>, VerifyError> {
        if fact.facts.len() != other.facts.len() {
            return Ok(None);
        }

        let mut matched_args: Vec<(Obj, Obj)> = Vec::new();
        for (fact_item, other_item) in fact.facts.iter().zip(other.facts.iter()) {
            let sub_matched_args = match self._verify_and_chain_atomic_facts_the_same_type_and_return_matched_args(fact_item, other_item)? {
                Some(value) => value,
                None => return Ok(None),
            };
            for matched_arg in sub_matched_args {
                matched_args.push(matched_arg);
            }
        }

        Ok(Some(matched_args))
    }

    pub fn _verify_and_fact_the_same_type_and_return_matched_args(&mut self, fact: &AndFact, other: &AndFact) -> Result<Option<Vec<(Obj, Obj)>>, VerifyError> {
        if fact.facts.len() != other.facts.len() {
            return Ok(None);
        }

        let mut matched_args: Vec<(Obj, Obj)> = Vec::new();
        for (fact_item, other_item) in fact.facts.iter().zip(other.facts.iter()) {
            let sub_matched_args = match self._verify_atomic_fact_the_same_type_and_return_matched_args(fact_item, other_item)? {
                Some(value) => value,
                None => return Ok(None),
            };
            for matched_arg in sub_matched_args {
                matched_args.push(matched_arg);
            }
        }

        Ok(Some(matched_args))
    }

    pub fn _verify_exist_fact_the_same_type_and_return_matched_args(&mut self, fact: &ExistFact, other: &ExistFact) -> Result<Option<Vec<(Obj, Obj)>>, VerifyError> {
        if fact.params_def_with_type.len() != other.params_def_with_type.len() {
            return Ok(None);
        }
        if fact.facts.len() != other.facts.len() {
            return Ok(None);
        }

        for (fact_param_def, other_param_def) in fact.params_def_with_type.iter().zip(other.params_def_with_type.iter()) {
            if fact_param_def.1.to_string() != other_param_def.1.to_string() {
                return Ok(None);
            }
            if fact_param_def.0.len() != other_param_def.0.len() {
                return Ok(None);
            }
        }

        let mut matched_args: Vec<(Obj, Obj)> = Vec::new();
        for (fact_item, other_item) in fact.facts.iter().zip(other.facts.iter()) {
            let sub_matched_args = match self._verify_or_and_chain_atomic_facts_the_same_type_and_return_matched_args(fact_item, other_item)? {
                Some(value) => value,
                None => return Ok(None),
            };
            for matched_arg in sub_matched_args {
                matched_args.push(matched_arg);
            }
        }

        Ok(Some(matched_args))
    }

    pub fn _verify_atomic_fact_the_same_type_and_return_matched_args(&mut self, _fact: &AtomicFact, _other: &AtomicFact) -> Result<Option<Vec<(Obj, Obj)>>, VerifyError> {

        Ok(None)
    }
}