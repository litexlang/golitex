use std::collections::HashMap;
use std::fmt;
use crate::stmt::definition_stmt::DefStructStmt;
use crate::fact::Fact;
use crate::stmt::definition_stmt::DefPropStmt;
use crate::stmt::define_algorithm_stmt::DefAlgoStmt;
use crate::fact::AtomicFact;
use crate::fact::ExistFact;
use crate::fact::ForallFact;
use crate::fact::OrFact;
use std::rc::Rc;
use crate::obj::FnSetObj;
use crate::obj::SetBuilder;
use crate::fact::ForallFactWithIff;
use crate::error::StoreFactError;
use crate::fact::EqualFact;
use crate::fact::AndFact;
use crate::fact::ChainFact;
use crate::fact::ExistOrAndChainAtomicFact;
pub struct Environment {
    pub defined_identifier_objs: HashMap<String, ()>,
    pub defined_props: HashMap<String, DefPropStmt>,
    pub defined_structs: HashMap<String, DefStructStmt>,
    pub defined_algorithms: HashMap<String, DefAlgoStmt>,

    pub known_equality: HashMap<String, Rc<Vec<String>>>,
    pub known_fn_in_fn_set: HashMap<String, FnSetObj>,
    pub known_set_equal_to_set_builder: HashMap<String, SetBuilder>,

    pub known_atomic_facts_with_more_than_2_args: HashMap<(String, bool), Vec<AtomicFact>>,
    pub known_atomic_facts_with_1_arg: HashMap<(String, bool), HashMap<String, ()>>,
    pub known_atomic_facts_with_2_args: HashMap<(String, bool), HashMap<(String, String), ()>>,
    
    pub known_exist_facts: HashMap<String, Vec<ExistFact>>,
    pub known_or_facts: HashMap<String, Vec<OrFact>>,
    pub known_atomic_facts_in_forall_facts: HashMap<(String, bool), Vec<(usize, Rc<ForallFact>)>>,
    pub known_exist_facts_in_forall_facts: HashMap<String, Vec<(usize, Rc<ForallFact>)>>,
    pub known_or_facts_in_forall_facts: HashMap<String, Vec<(usize, Rc<ForallFact>)>>,
    pub known_obj_is_well_defined: HashMap<String,()>,

    pub cache_well_defined_obj: HashMap<String, ()>,
    pub cache_known_fact: HashMap<String, (usize, usize)>,
}

impl Environment {
    pub fn new(objs: HashMap<String, ()>, props: HashMap<String, DefPropStmt>, structs: HashMap<String, DefStructStmt>, algorithms: HashMap<String, DefAlgoStmt>, known_equality: HashMap<String, Rc<Vec<String>>>, known_fn_in_fn_set: HashMap<String, FnSetObj>, known_set_equal_to_set_builder: HashMap<String, SetBuilder>, known_atomic_facts: HashMap<(String, bool), Vec<AtomicFact>>, known_atomic_facts_with_1_arg: HashMap<(String, bool), HashMap<String, ()>>, known_atomic_facts_with_2_args: HashMap<(String, bool), HashMap<(String, String), ()>>, known_exist_facts: HashMap<String, Vec<ExistFact>>, known_atomic_facts_in_forall_facts: HashMap<(String, bool), Vec<(usize, Rc<ForallFact>)>>, known_exist_facts_in_forall_facts: HashMap<String, Vec<(usize, Rc<ForallFact>)>>, known_or_facts: HashMap<String, Vec<OrFact>>, known_or_facts_in_forall_facts: HashMap<String, Vec<(usize, Rc<ForallFact>)>>, known_fn_obj_with_requirements_checked: HashMap<String,()>, cache_known_valid_obj: HashMap<String, ()>, cache_known_fact: HashMap<String, (usize, usize)>) -> Self {
        Environment {
            defined_identifier_objs: objs,
            defined_props: props,
            defined_structs: structs,
            defined_algorithms: algorithms,
            known_equality,
            known_fn_in_fn_set,
            known_set_equal_to_set_builder,
            known_atomic_facts_with_more_than_2_args: known_atomic_facts,
            known_atomic_facts_with_1_arg: known_atomic_facts_with_1_arg,
            known_atomic_facts_with_2_args: known_atomic_facts_with_2_args,
            known_exist_facts,
            known_atomic_facts_in_forall_facts,
            known_exist_facts_in_forall_facts,
            known_or_facts,
            known_or_facts_in_forall_facts,
            known_obj_is_well_defined: known_fn_obj_with_requirements_checked,
            cache_well_defined_obj: cache_known_valid_obj,
            cache_known_fact,
        }
    }
}

impl fmt::Display for Environment {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Environment {{\n")?;
        write!(f, "    objs: {:?}\n", self.defined_identifier_objs.len())?;
        write!(f, "    props: {:?}\n", self.defined_props.len())?;
        write!(f, "    structs: {:?}\n", self.defined_structs.len())?;
        write!(f, "    algorithms: {:?}\n", self.defined_algorithms.len())?;
        write!(f, "    known_equality: {:?}\n", self.known_equality.len())?;
        write!(f, "    known_fn_in_fn_set: {:?}\n", self.known_fn_in_fn_set.len())?;
        write!(f, "    known_set_equal_to_set_builder: {:?}\n", self.known_set_equal_to_set_builder.len())?;
        write!(f, "    known_atomic_facts_with_more_than_two_params: {:?}\n", self.known_atomic_facts_with_more_than_2_args.len())?;
        write!(f, "    known_atomic_facts_with_1_arg: {:?}\n", self.known_atomic_facts_with_1_arg.len())?;
        write!(f, "    known_atomic_facts_with_2_args: {:?}\n", self.known_atomic_facts_with_2_args.len())?;
        write!(f, "    known_exist_facts_with_more_than_two_params: {:?}\n", self.known_exist_facts.len())?;
        write!(f, "    known_or_facts_with_more_than_two_params: {:?}\n", self.known_or_facts.len())?;
        write!(f, "    known_atomic_facts_in_forall_facts: {:?}\n", self.known_atomic_facts_in_forall_facts.len())?;
        write!(f, "    known_exist_facts_in_forall_facts: {:?}\n", self.known_exist_facts_in_forall_facts.len())?;
        write!(f, "    known_or_facts_in_forall_facts: {:?}\n", self.known_or_facts_in_forall_facts.len())?;
        write!(f, "    known_fn_obj_with_requirements_checked: {:?}\n", self.known_obj_is_well_defined.len())?;
        write!(f, "    cache_known_valid_obj: {:?}\n", self.cache_well_defined_obj.len())?;
        write!(f, "    cache_known_fact: {:?}\n", self.cache_known_fact.len())?;
        write!(f, "}}")
    }
}

impl Environment {
    fn store_atomic_fact(&mut self, atomic_fact: AtomicFact) -> Result<(), StoreFactError> {
        match atomic_fact {
            AtomicFact::EqualFact(equal_fact) => self.store_equality(&equal_fact),
            _ => {
                let key = atomic_fact.key();
                let is_true = atomic_fact.is_true();
                if atomic_fact.args().len() == 1 {
                    let arg_key = atomic_fact.args()[0].to_string();
                    if let Some(map) = self.known_atomic_facts_with_1_arg.get_mut(&(key.clone(), is_true)) {
                        map.insert(arg_key, ());
                    } else {
                        self.known_atomic_facts_with_1_arg.insert((key, is_true), HashMap::from([(arg_key, ())]));
                    }
                } else if atomic_fact.args().len() == 2 {
                    let arg_key1 = atomic_fact.args()[0].to_string();
                    let arg_key2 = atomic_fact.args()[1].to_string();
                    if let Some(map) = self.known_atomic_facts_with_2_args.get_mut(&(key.clone(), is_true)) {
                        map.insert((arg_key1, arg_key2), ());
                    } else {
                        self.known_atomic_facts_with_2_args.insert((key, is_true), HashMap::from([((arg_key1, arg_key2), ())]));
                    }
                } else {
                    if let Some(vec_ref) = self.known_atomic_facts_with_more_than_2_args.get_mut(&(key.clone(), is_true)) {
                        vec_ref.push(atomic_fact);
                    } else {
                        self.known_atomic_facts_with_more_than_2_args.insert((key, is_true), vec![atomic_fact]);
                    }
                }
                Ok(())
            }
        }
    }

    fn store_exist_fact(&mut self, exist_fact: ExistFact) -> Result<(), StoreFactError> {
        let key = exist_fact.key();
        if let Some(vec_ref) = self.known_exist_facts.get_mut(&key) {
            vec_ref.push(exist_fact);
        } else {
            self.known_exist_facts.insert(key, vec![exist_fact]);
        }
        Ok(())
    }

    fn store_or_fact(&mut self, or_fact: OrFact) -> Result<(), StoreFactError> {
        let key = or_fact.key();
        if let Some(vec_ref) = self.known_or_facts.get_mut(&key) {
            vec_ref.push(or_fact);
        } else {
            self.known_or_facts.insert(key, vec![or_fact]);
        }
        Ok(())
    }

    fn store_atomic_fact_in_forall_fact(&mut self, atomic_fact_ref: &AtomicFact, index: usize, forall_fact: Rc<ForallFact>) -> Result<(), StoreFactError> {
        let key = atomic_fact_ref.key();
        let is_true = atomic_fact_ref.is_true();
        if let Some(vec_ref) = self.known_atomic_facts_in_forall_facts.get_mut(&(key.clone(), is_true)) {
            vec_ref.push((index, forall_fact));
        } else {
            self.known_atomic_facts_in_forall_facts.insert((key, is_true), vec![(index, forall_fact)]);
        }
        Ok(())
    }

    fn store_or_fact_in_forall_fact(&mut self, or_fact: &OrFact, index: usize, forall_fact: Rc<ForallFact>) -> Result<(), StoreFactError> {
        let key = or_fact.key();
        if let Some(vec_ref) = self.known_or_facts_in_forall_facts.get_mut(&key) {
            vec_ref.push((index, forall_fact));
        } else {
            self.known_or_facts_in_forall_facts.insert(key, vec![(index, forall_fact)]);
        }
        Ok(())
    }

    fn store_a_fact_in_forall_fact(&mut self, fact: &ExistOrAndChainAtomicFact, index: usize, forall_fact: Rc<ForallFact>) -> Result<(), StoreFactError> {
        match fact {
            ExistOrAndChainAtomicFact::AtomicFact(spec_fact) => {
                self.store_atomic_fact_in_forall_fact(&spec_fact, index, forall_fact)
            }
            ExistOrAndChainAtomicFact::OrFact(or_fact) => self.store_or_fact_in_forall_fact(&or_fact, index, forall_fact),
            ExistOrAndChainAtomicFact::AndFact(and_fact) => self.store_and_fact_in_forall_fact(&and_fact, index, forall_fact),
            ExistOrAndChainAtomicFact::ChainFact(chain_fact) => self.store_chain_fact_in_forall_fact(&chain_fact, index, forall_fact),
            ExistOrAndChainAtomicFact::ExistFact(exist_fact) => self.store_exist_fact_in_forall_fact(&exist_fact, index, forall_fact),
        }
    }

    fn store_chain_fact_in_forall_fact(&mut self, chain_fact: &ChainFact, index: usize, forall_fact: Rc<ForallFact>) -> Result<(), StoreFactError> {
        for fact in chain_fact.facts()?.iter() {
            self.store_a_fact_in_forall_fact(&ExistOrAndChainAtomicFact::AtomicFact(fact.clone()), index, forall_fact.clone())?;
        }
        Ok(())
    }

    fn store_exist_fact_in_forall_fact(&mut self, exist_fact: &ExistFact, index: usize, forall_fact: Rc<ForallFact>) -> Result<(), StoreFactError> {
        let key = exist_fact.key();
        if let Some(vec_ref) = self.known_exist_facts_in_forall_facts.get_mut(&key) {
            vec_ref.push((index, forall_fact));
        } else {
            self.known_exist_facts_in_forall_facts.insert(key, vec![(index, forall_fact)]);
        }
        Ok(())
    }

    fn store_and_fact_in_forall_fact(&mut self, and_fact: &AndFact, index: usize, forall_fact: Rc<ForallFact>) -> Result<(), StoreFactError> {
        for fact in and_fact.facts.iter() {
            self.store_a_fact_in_forall_fact(&ExistOrAndChainAtomicFact::AtomicFact(fact.clone()), index, forall_fact.clone())?;
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
        for fact in and_fact.facts.iter() {
            self.store_atomic_fact(fact.clone())?;
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
            Fact::ChainFact(chain_fact) => self.store_chain_fact(chain_fact),
            Fact::ForallFact(forall_fact) => self.store_forall_fact(Rc::new(forall_fact)),
            Fact::ForallFactWithIff(forall_fact_with_iff) => self.store_forall_fact_with_iff(forall_fact_with_iff),
        }
    }

    fn store_chain_fact(&mut self, chain_fact: ChainFact) -> Result<(), StoreFactError> {
        for fact in chain_fact.facts()?.iter() {
            self.store_atomic_fact(fact.clone())?;
        }
        Ok(())
    }

    pub fn store_equality(&mut self, equality: &EqualFact) -> Result<(), StoreFactError> {
        let left_as_string = equality.left.to_string();
        let right_as_string = equality.right.to_string();
        if left_as_string == right_as_string {
            return Ok(());
        }

        let left_rc = self.known_equality.get(&left_as_string).map(Rc::clone);
        let right_rc = self.known_equality.get(&right_as_string).map(Rc::clone);

        match (left_rc, right_rc) {
            (Some(ref left_r), Some(ref right_r)) => {
                if Rc::ptr_eq(left_r, right_r) {
                    return Ok(());
                }
                // 1. 合并两个等价类：新 vec = 两个 vec 的并，所有指向任一的 key 都改为指向新 Rc
                let merged: Vec<String> = {
                    let a: &Vec<String> = left_r.as_ref();
                    let b: &Vec<String> = right_r.as_ref();
                    let mut v: Vec<String> = a.iter().chain(b.iter()).cloned().collect();
                    v.sort();
                    v.dedup();
                    v
                };
                let new_rc = Rc::new(merged);
                for k in new_rc.iter() {
                    self.known_equality.insert(k.clone(), Rc::clone(&new_rc));
                }
            }
            (Some(ref rc), None) => {
                // 2. 仅 right 不在：把 right 加入 left 所在等价类（Rc<Vec> 不可变，新建 Vec 并更新所有指向该类的 key）
                let mut new_vec = (**rc).clone();
                new_vec.push(right_as_string.clone());
                let new_rc = Rc::new(new_vec);
                let keys_to_update: Vec<String> = self.known_equality.iter()
                    .filter(|(_, v)| Rc::ptr_eq(v, rc))
                    .map(|(k, _)| k.clone())
                    .collect();
                for k in keys_to_update {
                    self.known_equality.insert(k, Rc::clone(&new_rc));
                }
                self.known_equality.insert(right_as_string, new_rc);
            }
            (None, Some(ref rc)) => {
                // 2. 仅 left 不在：把 left 加入 right 所在等价类
                let mut new_vec = (**rc).clone();
                new_vec.push(left_as_string.clone());
                let new_rc = Rc::new(new_vec);
                let keys_to_update: Vec<String> = self.known_equality.iter()
                    .filter(|(_, v)| Rc::ptr_eq(v, rc))
                    .map(|(k, _)| k.clone())
                    .collect();
                for k in keys_to_update {
                    self.known_equality.insert(k, Rc::clone(&new_rc));
                }
                self.known_equality.insert(left_as_string, new_rc);
            }
            (None, None) => {
                // 3. 两个都不在：新建等价类 [left, right]
                let vec = vec![left_as_string.clone(), right_as_string.clone()];
                let new_rc = Rc::new(vec);
                self.known_equality.insert(left_as_string.clone(), Rc::clone(&new_rc));
                self.known_equality.insert(right_as_string, new_rc);
            }
        }
        Ok(())
    }
}

impl Environment {
    pub fn new_empty_env() -> Self {
        Environment::new(HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new(), HashMap::new())
    }
}