use std::collections::HashMap;
use std::fmt;
use crate::fact::Fact;
use crate::definition_stmt::DefPropStmt;
use crate::definition_stmt::DefSetTemplateStmt;
use crate::define_algorithm_stmt::DefineAlgorithmStmt;
use crate::atomic_fact::AtomicFact;
use crate::exist_fact::ExistFact;
use crate::forall_fact::ForallFact;
use crate::or_fact::OrFact;
use std::rc::Rc;
use crate::obj::FnSetObj;
use crate::obj::SetBuilder;
use crate::or_fact_or_and_fact_or_specific_fact::OrFactOrAndFactOrSpecFact;
use crate::specific_fact::SpecFact;
use crate::and_fact::AndFact;
use crate::forall_fact_with_iff::ForallFactWithIff;
use crate::errors::StoreFactError;

pub struct Environment {
    pub defined_objs: HashMap<String, ()>,
    pub defined_props: HashMap<String, DefPropStmt>,
    pub defined_set_templates: HashMap<String, DefSetTemplateStmt>,
    pub defined_algorithms: HashMap<String, DefineAlgorithmStmt>,

    pub known_equality: HashMap<String, Rc<Vec<String>>>,
    pub known_fn_in_fn_set: HashMap<String, FnSetObj>,
    pub known_set_equal_to_set_builder: HashMap<String, SetBuilder>,
    pub known_atomic_facts: HashMap<(String, bool), Vec<AtomicFact>>,
    pub known_exist_facts: HashMap<(String, bool), Vec<ExistFact>>,
    pub known_or_facts: HashMap<String, Vec<OrFact>>,
    pub known_atomic_facts_in_forall_facts: HashMap<(String, bool), Vec<(usize, Rc<ForallFact>)>>,
    pub known_exist_facts_in_forall_facts: HashMap<(String, bool), Vec<(usize, Rc<ForallFact>)>>,
    pub known_or_facts_in_forall_facts: HashMap<String, Vec<(usize, Rc<ForallFact>)>>,
    pub known_obj_is_well_defined: HashMap<String,()>,
}

impl Environment {
    pub fn new(objs: HashMap<String, ()>, props: HashMap<String, DefPropStmt>, set_templates: HashMap<String, DefSetTemplateStmt>, algorithms: HashMap<String, DefineAlgorithmStmt>, known_equality: HashMap<String, Rc<Vec<String>>>, known_fn_in_fn_set: HashMap<String, FnSetObj>, known_set_equal_to_set_builder: HashMap<String, SetBuilder>, known_atomic_facts: HashMap<(String, bool), Vec<AtomicFact>>, known_exist_facts: HashMap<(String, bool), Vec<ExistFact>>, known_atomic_facts_in_forall_facts: HashMap<(String, bool), Vec<(usize, Rc<ForallFact>)>>, known_exist_facts_in_forall_facts: HashMap<(String, bool), Vec<(usize, Rc<ForallFact>)>>, known_or_facts: HashMap<String, Vec<OrFact>>, known_or_facts_in_forall_facts: HashMap<String, Vec<(usize, Rc<ForallFact>)>>, known_fn_obj_with_requirements_checked: HashMap<String,()>) -> Self {
        Environment {
            defined_objs: objs,
            defined_props: props,
            defined_set_templates: set_templates,
            defined_algorithms: algorithms,
            known_equality,
            known_fn_in_fn_set,
            known_set_equal_to_set_builder,
            known_atomic_facts,
            known_exist_facts,
            known_atomic_facts_in_forall_facts,
            known_exist_facts_in_forall_facts,
            known_or_facts,
            known_or_facts_in_forall_facts,
            known_obj_is_well_defined: known_fn_obj_with_requirements_checked,
        }
    }
}

impl fmt::Display for Environment {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Environment {{\n")?;
        write!(f, "    objs: {:?}\n", self.defined_objs.len())?;
        write!(f, "    props: {:?}\n", self.defined_props.len())?;
        write!(f, "    set_templates: {:?}\n", self.defined_set_templates.len())?;
        write!(f, "    algorithms: {:?}\n", self.defined_algorithms.len())?;
        write!(f, "    known_equality: {:?}\n", self.known_equality.len())?;
        write!(f, "    known_fn_in_fn_set: {:?}\n", self.known_fn_in_fn_set.len())?;
        write!(f, "    known_set_equal_to_set_builder: {:?}\n", self.known_set_equal_to_set_builder.len())?;
        write!(f, "    known_atomic_facts_with_more_than_two_params: {:?}\n", self.known_atomic_facts.len())?;
        write!(f, "    known_exist_facts_with_more_than_two_params: {:?}\n", self.known_exist_facts.len())?;
        write!(f, "    known_or_facts_with_more_than_two_params: {:?}\n", self.known_or_facts.len())?;
        write!(f, "    known_atomic_facts_in_forall_facts: {:?}\n", self.known_atomic_facts_in_forall_facts.len())?;
        write!(f, "    known_exist_facts_in_forall_facts: {:?}\n", self.known_exist_facts_in_forall_facts.len())?;
        write!(f, "    known_or_facts_in_forall_facts: {:?}\n", self.known_or_facts_in_forall_facts.len())?;
        write!(f, "    known_fn_obj_with_requirements_checked: {:?}\n", self.known_obj_is_well_defined.len())?;
        write!(f, "}}")
    }
}

impl Environment {
    fn store_atomic_fact(&mut self, atomic_fact: AtomicFact) -> Result<(), StoreFactError> {
        let key = atomic_fact.key();
        let is_true = atomic_fact.is_true();
        if self.known_atomic_facts.contains_key(&(key, is_true)) {
            self.known_atomic_facts.get_mut(&(atomic_fact.key(), is_true)).unwrap().push(atomic_fact);
        } else {
            self.known_atomic_facts.insert((atomic_fact.key(), is_true), vec![atomic_fact]);
        }
        Ok(())
    }

    fn store_exist_fact(&mut self, exist_fact: ExistFact) -> Result<(), StoreFactError> {
        let key = exist_fact.key();
        let is_true = exist_fact.is_true();
        if self.known_exist_facts.contains_key(&(key, is_true)) {
            self.known_exist_facts.get_mut(&(exist_fact.key(), is_true)).unwrap().push(exist_fact);
        } else {
            self.known_exist_facts.insert((exist_fact.key(), is_true), vec![exist_fact]);
        }
        Ok(())
    }

    fn store_or_fact(&mut self, or_fact: OrFact) -> Result<(), StoreFactError> {
        let key = or_fact.key();
        if self.known_or_facts.contains_key(&key) {
            self.known_or_facts.get_mut(&key).unwrap().push(or_fact);
        } else {
            self.known_or_facts.insert(key, vec![or_fact]);
        }
        Ok(())
    }

    fn store_atomic_fact_in_forall_fact(&mut self, atomic_fact_ref: &AtomicFact, index: usize, forall_fact: Rc<ForallFact>) -> Result<(), StoreFactError> {
        let key = atomic_fact_ref.key();
        let is_true = atomic_fact_ref.is_true();
        if self.known_atomic_facts_in_forall_facts.contains_key(&(key, is_true)) {
            self.known_atomic_facts_in_forall_facts.get_mut(&(atomic_fact_ref.key(), is_true)).unwrap().push((index, forall_fact));
        } else {
            self.known_atomic_facts_in_forall_facts.insert((atomic_fact_ref.key(), is_true), vec![(index, forall_fact)]);
        }
        Ok(())
    }

    fn store_exist_fact_in_forall_fact(&mut self, exist_fact_ref: &ExistFact, index: usize, forall_fact: Rc<ForallFact>) -> Result<(), StoreFactError> {
        let key = exist_fact_ref.key();
        let is_true = exist_fact_ref.is_true();
        if self.known_exist_facts_in_forall_facts.contains_key(&(key, is_true)) {
            self.known_exist_facts_in_forall_facts.get_mut(&(exist_fact_ref.key(), is_true)).unwrap().push((index, forall_fact));
        } else {
            self.known_exist_facts_in_forall_facts.insert((exist_fact_ref.key(), is_true), vec![(index, forall_fact)]);
        }
        Ok(())
    }

    fn store_or_fact_in_forall_fact(&mut self, or_fact: &OrFact, index: usize, forall_fact: Rc<ForallFact>) -> Result<(), StoreFactError> {
        let key = or_fact.key();
        if self.known_or_facts_in_forall_facts.contains_key(&key) {
            self.known_or_facts_in_forall_facts.get_mut(&key).unwrap().push((index, forall_fact));
        } else {
            self.known_or_facts_in_forall_facts.insert(key, vec![(index, forall_fact)]);
        }
        Ok(())
    }

    fn store_a_fact_in_forall_fact(&mut self, fact: &OrFactOrAndFactOrSpecFact, index: usize, forall_fact: Rc<ForallFact>) -> Result<(), StoreFactError> {
        match fact {
            OrFactOrAndFactOrSpecFact::SpecFact(spec_fact) => {
                match spec_fact {
                    SpecFact::AtomicFact(atomic_fact) => self.store_atomic_fact_in_forall_fact(&atomic_fact, index, forall_fact),
                    SpecFact::ExistFact(exist_fact) => self.store_exist_fact_in_forall_fact(&exist_fact, index, forall_fact),
                }
            }
            OrFactOrAndFactOrSpecFact::OrFact(or_fact) => self.store_or_fact_in_forall_fact(&or_fact, index, forall_fact),
            OrFactOrAndFactOrSpecFact::AndFact(and_fact) => self.store_and_fact_in_forall_fact(&and_fact, index, forall_fact),
        }
    }

    fn store_and_fact_in_forall_fact(&mut self, and_fact: &AndFact, index: usize, forall_fact: Rc<ForallFact>) -> Result<(), StoreFactError> {
        match and_fact {
            AndFact::AndSpecFacts(and_spec_facts) => {
                for fact in and_spec_facts.facts.iter() {
                    match fact {
                        SpecFact::AtomicFact(atomic_fact) => self.store_atomic_fact_in_forall_fact(&atomic_fact, index, forall_fact.clone())?,
                        SpecFact::ExistFact(exist_fact) => self.store_exist_fact_in_forall_fact(&exist_fact, index, forall_fact.clone())?,
                    }
                }
            }
            AndFact::ChainFact(chain_fact) => {
                let facts = chain_fact.facts();
                if facts.is_err() {
                    return Err(StoreFactError::new(&format!("{}", facts.err().unwrap())));
                }
                for fact in facts.unwrap().iter() {
                    match fact {
                        SpecFact::AtomicFact(atomic_fact) => self.store_atomic_fact_in_forall_fact(&atomic_fact, index, forall_fact.clone())?,
                        SpecFact::ExistFact(exist_fact) => self.store_exist_fact_in_forall_fact(&exist_fact, index, forall_fact.clone())?,
                    }
                }
            }
        }
        Ok(())
    }

    fn store_forall_fact(&mut self, forall_fact: Rc<ForallFact>) -> Result<(), StoreFactError> {
        for (index, fact) in forall_fact.then_facts.iter().enumerate() {
            self.store_a_fact_in_forall_fact(fact, index, forall_fact.clone())?;
        }
        Ok(())
    }

    fn store_and_fact(&mut self, and_fact: AndFact) -> Result<(), StoreFactError> {
        match and_fact {
            AndFact::AndSpecFacts(and_spec_facts) => {
                for fact in and_spec_facts.facts {
                    match fact {
                        SpecFact::AtomicFact(atomic_fact) => self.store_atomic_fact(atomic_fact)?,
                        SpecFact::ExistFact(exist_fact) => self.store_exist_fact(exist_fact)?,
                    }
                }
            }
            AndFact::ChainFact(chain_fact) => {
                let facts = chain_fact.facts();
                if facts.is_err() {
                    return Err(StoreFactError::new(&format!("{}", facts.err().unwrap())));
                }
                for fact in facts.unwrap() {
                    match fact {
                        SpecFact::AtomicFact(atomic_fact) => self.store_atomic_fact(atomic_fact)?,
                        SpecFact::ExistFact(exist_fact) => self.store_exist_fact(exist_fact)?,
                    }
                }
            }
        }
        Ok(())
    }

    fn store_forall_fact_with_iff(&mut self, forall_fact_with_iff: ForallFactWithIff) -> Result<(), StoreFactError> {
        let (forall_then_implies_iff, forall_iff_implies_then) = forall_fact_with_iff.to_two_forall_facts();
        self.store_forall_fact(Rc::new(forall_then_implies_iff))?;
        self.store_forall_fact(Rc::new(forall_iff_implies_then))?;
        Ok(())
    }

    pub fn store_fact(&mut self, fact: Fact) -> Result<(), StoreFactError> {
        match fact {
            Fact::AtomicFact(atomic_fact) => self.store_atomic_fact(atomic_fact),
            Fact::ExistFact(exist_fact) => self.store_exist_fact(exist_fact),
            Fact::OrFact(or_fact) => self.store_or_fact(or_fact),
            Fact::AndFact(and_fact) => self.store_and_fact(and_fact),
            Fact::ForallFact(forall_fact) => self.store_forall_fact(Rc::new(forall_fact)),
            Fact::ForallFactWithIff(forall_fact_with_iff) => self.store_forall_fact_with_iff(forall_fact_with_iff),
        }
    }
}