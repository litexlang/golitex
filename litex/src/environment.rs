use std::collections::HashMap;
use std::fmt;
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

pub struct Environment {
    // defined things in local scope
    pub defined_objs: HashMap<String, ()>,
    pub defined_props: HashMap<String, DefPropStmt>,
    pub defined_set_templates: HashMap<String, DefSetTemplateStmt>,
    pub defined_algorithms: HashMap<String, DefineAlgorithmStmt>,

    // known facts
    pub known_equality: HashMap<String, Rc<Vec<String>>>,
    pub known_fn_in_fn_set: HashMap<String, FnSetObj>,
    pub known_set_equal_to_set_builder: HashMap<String, SetBuilder>,
    pub known_atomic_facts: HashMap<(String, bool), Vec<AtomicFact>>,
    pub known_exist_facts: HashMap<(String, bool), Vec<ExistFact>>,
    pub known_or_facts: HashMap<String, Vec<OrFact>>,
    pub known_atomic_facts_in_forall_facts: HashMap<(String, bool), Vec<(i32, Rc<ForallFact>)>>,
    pub known_exist_facts_in_forall_facts: HashMap<(String, bool), Vec<(i32, Rc<ForallFact>)>>,
    pub known_or_facts_in_forall_facts: HashMap<String, Vec<(i32, Rc<ForallFact>)>>,
    pub known_obj_is_well_defined: HashMap<String,()>,
}

impl Environment {
    pub fn new(objs: HashMap<String, ()>, props: HashMap<String, DefPropStmt>, set_templates: HashMap<String, DefSetTemplateStmt>, algorithms: HashMap<String, DefineAlgorithmStmt>, known_equality: HashMap<String, Rc<Vec<String>>>, known_fn_in_fn_set: HashMap<String, FnSetObj>, known_set_equal_to_set_builder: HashMap<String, SetBuilder>, known_atomic_facts: HashMap<(String, bool), Vec<AtomicFact>>, known_exist_facts: HashMap<(String, bool), Vec<ExistFact>>, known_atomic_facts_in_forall_facts: HashMap<(String, bool), Vec<(i32, Rc<ForallFact>)>>, known_exist_facts_in_forall_facts: HashMap<(String, bool), Vec<(i32, Rc<ForallFact>)>>, known_or_facts: HashMap<String, Vec<OrFact>>, known_or_facts_in_forall_facts: HashMap<String, Vec<(i32, Rc<ForallFact>)>>, known_fn_obj_with_requirements_checked: HashMap<String,()>) -> Self {
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
    pub fn store_atomic_fact(&mut self, atomic_fact: AtomicFact) {
        let key = atomic_fact.key();
        let is_true = atomic_fact.is_true();
        if self.known_atomic_facts.contains_key(&(key, is_true)) {
            self.known_atomic_facts.get_mut(&(atomic_fact.key(), is_true)).unwrap().push(atomic_fact);
        } else {
            self.known_atomic_facts.insert((atomic_fact.key(), is_true), vec![atomic_fact]);
        }
    }

    pub fn store_exist_fact(&mut self, exist_fact: ExistFact) {
        let key = exist_fact.key();
        let is_true = exist_fact.is_true();
        if self.known_exist_facts.contains_key(&(key, is_true)) {
            self.known_exist_facts.get_mut(&(exist_fact.key(), is_true)).unwrap().push(exist_fact);
        } else {
            self.known_exist_facts.insert((exist_fact.key(), is_true), vec![exist_fact]);
        }
    }

    pub fn store_atomic_fact_in_forall_fact(&mut self, atomic_fact_ref: &AtomicFact, index: i32, forall_fact: Rc<ForallFact>) {
        let key = atomic_fact_ref.key();
        let is_true = atomic_fact_ref.is_true();
        if self.known_atomic_facts_in_forall_facts.contains_key(&(key, is_true)) {
            self.known_atomic_facts_in_forall_facts.get_mut(&(atomic_fact_ref.key(), is_true)).unwrap().push((index, forall_fact));
        } else {
            self.known_atomic_facts_in_forall_facts.insert((atomic_fact_ref.key(), is_true), vec![(index, forall_fact)]);
        }
    }

    pub fn store_exist_fact_in_forall_fact(&mut self, exist_fact_ref: &ExistFact, index: i32, forall_fact: Rc<ForallFact>) {
        let key = exist_fact_ref.key();
        let is_true = exist_fact_ref.is_true();
        if self.known_exist_facts_in_forall_facts.contains_key(&(key, is_true)) {
            self.known_exist_facts_in_forall_facts.get_mut(&(exist_fact_ref.key(), is_true)).unwrap().push((index, forall_fact));
        } else {
            self.known_exist_facts_in_forall_facts.insert((exist_fact_ref.key(), is_true), vec![(index, forall_fact)]);
        }
    }

    pub fn store_or_fact_or_and_fact_or_spec_fact_in_forall_fact(&mut self, fact: &OrFactOrAndFactOrSpecFact, index: i32, forall_fact: Rc<ForallFact>) {
        match fact {
            OrFactOrAndFactOrSpecFact::SpecFact(spec_fact) => {
                match spec_fact {
                    SpecFact::AtomicFact(atomic_fact) => self.store_atomic_fact_in_forall_fact(&atomic_fact, index, forall_fact),
                    SpecFact::ExistFact(exist_fact) => self.store_exist_fact_in_forall_fact(&exist_fact, index, forall_fact),
                }
            }
            _ => panic!("Invalid fact type"),
        }
    }
}