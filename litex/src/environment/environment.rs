use crate::error::StoreFactError;
use crate::fact::AndFact;
use crate::fact::AtomicFact;
use crate::fact::ChainFact;
use crate::fact::EqualFact;
use crate::fact::ExistFact;
use crate::fact::ExistOrAndChainAtomicFact;
use crate::fact::Fact;
use crate::fact::ForallFact;
use crate::fact::ForallFactWithIff;
use crate::fact::OrAndChainAtomicFact;
use crate::fact::OrFact;
use crate::obj::Cart;
use crate::obj::FnSetObj;
use crate::obj::Obj;
use crate::obj::SetBuilder;
use crate::stmt::define_algorithm_stmt::DefAlgoStmt;
use crate::stmt::definition_stmt::{DefPropWithMeaningStmt, DefPropWithoutMeaningStmt};
use crate::stmt::definition_stmt::{DefStructWithFieldsStmt, DefStructWithNoFieldStmt};
use crate::stmt::parameter_def::ParamDefWithParamType;
use std::collections::HashMap;
use std::fmt;
use std::rc::Rc;
pub struct Environment {
    pub defined_identifier_objs: HashMap<String, ()>,
    pub defined_props_with_meaning: HashMap<String, DefPropWithMeaningStmt>,
    pub defined_structs_with_fields: HashMap<String, DefStructWithFieldsStmt>,
    pub defined_structs_with_no_field: HashMap<String, DefStructWithNoFieldStmt>,
    pub defined_props_without_meaning: HashMap<String, DefPropWithoutMeaningStmt>,
    pub defined_algorithms: HashMap<String, DefAlgoStmt>,

    pub known_equality: HashMap<String, Rc<Vec<Obj>>>,
    pub known_fn_in_fn_set: HashMap<String, FnSetObj>,
    pub known_set_equal_to_set_builder: HashMap<String, SetBuilder>,

    pub known_atomic_facts_with_0_or_more_than_2_args: HashMap<(String, bool), Vec<AtomicFact>>,
    pub known_atomic_facts_with_1_arg: HashMap<(String, bool), HashMap<String, AtomicFact>>,
    pub known_atomic_facts_with_2_args:
        HashMap<(String, bool), HashMap<(String, String), AtomicFact>>,

    pub known_exist_facts: HashMap<String, Vec<ExistFact>>,
    pub known_or_facts: HashMap<String, Vec<OrFact>>,
    pub known_atomic_facts_in_forall_facts:
        HashMap<(String, bool), Vec<(AtomicFact, Rc<KnownForallFactParamsAndDom>)>>,
    pub known_exist_facts_in_forall_facts:
        HashMap<String, Vec<(ExistFact, Rc<KnownForallFactParamsAndDom>)>>,
    pub known_or_facts_in_forall_facts:
        HashMap<String, Vec<(OrFact, Rc<KnownForallFactParamsAndDom>)>>,
    pub known_obj_is_well_defined: HashMap<String, ()>,
    pub known_atom_in_fn_set: HashMap<String, FnSetObj>,
    pub known_tuple_obj_in_what_cart: HashMap<String, Cart>,

    pub cache_well_defined_obj: HashMap<String, ()>,
    pub cache_known_fact: HashMap<String, (usize, usize)>,
}

impl Environment {
    pub fn new(
        objs: HashMap<String, ()>,
        props: HashMap<String, DefPropWithMeaningStmt>,
        structs_with_fields: HashMap<String, DefStructWithFieldsStmt>,
        structs_with_no_field: HashMap<String, DefStructWithNoFieldStmt>,
        props_without_meaning: HashMap<String, DefPropWithoutMeaningStmt>,
        algorithms: HashMap<String, DefAlgoStmt>,
        known_equality: HashMap<String, Rc<Vec<Obj>>>,
        known_fn_in_fn_set: HashMap<String, FnSetObj>,
        known_set_equal_to_set_builder: HashMap<String, SetBuilder>,
        known_atomic_facts_with_0_or_more_than_2_args: HashMap<(String, bool), Vec<AtomicFact>>,
        known_atomic_facts_with_1_arg: HashMap<(String, bool), HashMap<String, AtomicFact>>,
        known_atomic_facts_with_2_args: HashMap<
            (String, bool),
            HashMap<(String, String), AtomicFact>,
        >,
        known_exist_facts: HashMap<String, Vec<ExistFact>>,
        known_atomic_facts_in_forall_facts: HashMap<
            (String, bool),
            Vec<(AtomicFact, Rc<KnownForallFactParamsAndDom>)>,
        >,
        known_exist_facts_in_forall_facts: HashMap<
            String,
            Vec<(ExistFact, Rc<KnownForallFactParamsAndDom>)>,
        >,
        known_or_facts: HashMap<String, Vec<OrFact>>,
        known_or_facts_in_forall_facts: HashMap<
            String,
            Vec<(OrFact, Rc<KnownForallFactParamsAndDom>)>,
        >,
        known_obj_is_well_defined: HashMap<String, ()>,
        known_atom_in_fn_set: HashMap<String, FnSetObj>,
        known_tuple_dim_obj: HashMap<String, Cart>,
        cache_known_valid_obj: HashMap<String, ()>,
        cache_known_fact: HashMap<String, (usize, usize)>,
    ) -> Self {
        Environment {
            defined_identifier_objs: objs,
            defined_props_with_meaning: props,
            defined_structs_with_fields: structs_with_fields,
            defined_structs_with_no_field: structs_with_no_field,
            defined_props_without_meaning: props_without_meaning,
            defined_algorithms: algorithms,
            known_equality,
            known_fn_in_fn_set,
            known_set_equal_to_set_builder,
            known_atomic_facts_with_0_or_more_than_2_args,
            known_atomic_facts_with_1_arg: known_atomic_facts_with_1_arg,
            known_atomic_facts_with_2_args: known_atomic_facts_with_2_args,
            known_exist_facts,
            known_atomic_facts_in_forall_facts,
            known_exist_facts_in_forall_facts,
            known_or_facts,
            known_or_facts_in_forall_facts,
            known_obj_is_well_defined,
            known_atom_in_fn_set,
            known_tuple_obj_in_what_cart: known_tuple_dim_obj,
            cache_well_defined_obj: cache_known_valid_obj,
            cache_known_fact,
        }
    }
}

impl fmt::Display for Environment {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Environment {{\n")?;
        write!(f, "    objs: {:?}\n", self.defined_identifier_objs.len())?;
        write!(
            f,
            "    props_with_meaning: {:?}\n",
            self.defined_props_with_meaning.len()
        )?;
        write!(
            f,
            "    structs_with_fields: {:?}\n",
            self.defined_structs_with_fields.len()
        )?;
        write!(
            f,
            "    structs_with_no_field: {:?}\n",
            self.defined_structs_with_no_field.len()
        )?;
        write!(f, "    algorithms: {:?}\n", self.defined_algorithms.len())?;
        write!(f, "    known_equality: {:?}\n", self.known_equality.len())?;
        write!(
            f,
            "    known_fn_in_fn_set: {:?}\n",
            self.known_fn_in_fn_set.len()
        )?;
        write!(
            f,
            "    known_set_equal_to_set_builder: {:?}\n",
            self.known_set_equal_to_set_builder.len()
        )?;
        write!(
            f,
            "    known_atomic_facts_with_0_or_more_than_two_params: {:?}\n",
            self.known_atomic_facts_with_0_or_more_than_2_args.len()
        )?;
        write!(
            f,
            "    known_atomic_facts_with_1_arg: {:?}\n",
            self.known_atomic_facts_with_1_arg.len()
        )?;
        write!(
            f,
            "    known_atomic_facts_with_2_args: {:?}\n",
            self.known_atomic_facts_with_2_args.len()
        )?;
        write!(
            f,
            "    known_exist_facts_with_more_than_two_params: {:?}\n",
            self.known_exist_facts.len()
        )?;
        write!(
            f,
            "    known_or_facts_with_more_than_two_params: {:?}\n",
            self.known_or_facts.len()
        )?;
        write!(
            f,
            "    known_atomic_facts_in_forall_facts: {:?}\n",
            self.known_atomic_facts_in_forall_facts.len()
        )?;
        write!(
            f,
            "    known_exist_facts_in_forall_facts: {:?}\n",
            self.known_exist_facts_in_forall_facts.len()
        )?;
        write!(
            f,
            "    known_or_facts_in_forall_facts: {:?}\n",
            self.known_or_facts_in_forall_facts.len()
        )?;
        write!(
            f,
            "    known_obj_is_well_defined: {:?}\n",
            self.known_obj_is_well_defined.len()
        )?;
        write!(
            f,
            "    known_obj_in_fn_set: {:?}\n",
            self.known_atom_in_fn_set.len()
        )?;
        write!(
            f,
            "    cache_known_valid_obj: {:?}\n",
            self.cache_well_defined_obj.len()
        )?;
        write!(
            f,
            "    cache_known_fact: {:?}\n",
            self.cache_known_fact.len()
        )?;
        write!(f, "}}")
    }
}

impl Environment {
    pub fn store_atomic_fact_by_ref(&mut self, atomic_fact: &AtomicFact) -> Result<(), StoreFactError> {
        self.store_atomic_fact(atomic_fact.clone())
    }

    fn store_atomic_fact(&mut self, atomic_fact: AtomicFact) -> Result<(), StoreFactError> {
        match atomic_fact {
            AtomicFact::EqualFact(equal_fact) => self.store_equality(&equal_fact),
            _ => {
                let key = atomic_fact.key();
                let is_true = atomic_fact.is_true();
                if atomic_fact.args().len() == 1 {
                    let arg_key = atomic_fact.args()[0].to_string();
                    if let Some(map) = self
                        .known_atomic_facts_with_1_arg
                        .get_mut(&(key.clone(), is_true))
                    {
                        map.insert(arg_key, atomic_fact);
                    } else {
                        self.known_atomic_facts_with_1_arg
                            .insert((key, is_true), HashMap::from([(arg_key, atomic_fact)]));
                    }
                } else if atomic_fact.args().len() == 2 {
                    let arg_key1 = atomic_fact.args()[0].to_string();
                    let arg_key2 = atomic_fact.args()[1].to_string();
                    if let Some(map) = self
                        .known_atomic_facts_with_2_args
                        .get_mut(&(key.clone(), is_true))
                    {
                        map.insert((arg_key1, arg_key2), atomic_fact);
                    } else {
                        self.known_atomic_facts_with_2_args.insert(
                            (key, is_true),
                            HashMap::from([((arg_key1, arg_key2), atomic_fact)]),
                        );
                    }
                } else {
                    if let Some(vec_ref) = self
                        .known_atomic_facts_with_0_or_more_than_2_args
                        .get_mut(&(key.clone(), is_true))
                    {
                        vec_ref.push(atomic_fact);
                    } else {
                        self.known_atomic_facts_with_0_or_more_than_2_args
                            .insert((key, is_true), vec![atomic_fact]);
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

    fn store_atomic_fact_in_forall_fact(
        &mut self,
        atomic_fact_ref: &AtomicFact,
        forall_params_and_dom: Rc<KnownForallFactParamsAndDom>,
    ) -> Result<(), StoreFactError> {
        let key = atomic_fact_ref.key();
        let is_true = atomic_fact_ref.is_true();
        if let Some(vec_ref) = self
            .known_atomic_facts_in_forall_facts
            .get_mut(&(key.clone(), is_true))
        {
            vec_ref.push((atomic_fact_ref.clone(), forall_params_and_dom));
        } else {
            self.known_atomic_facts_in_forall_facts.insert(
                (key, is_true),
                vec![(atomic_fact_ref.clone(), forall_params_and_dom)],
            );
        }
        Ok(())
    }

    fn store_or_fact_in_forall_fact(
        &mut self,
        or_fact: &OrFact,
        forall_params_and_dom: Rc<KnownForallFactParamsAndDom>,
    ) -> Result<(), StoreFactError> {
        let key = or_fact.key();
        if let Some(vec_ref) = self.known_or_facts_in_forall_facts.get_mut(&key) {
            vec_ref.push((or_fact.clone(), forall_params_and_dom));
        } else {
            self.known_or_facts_in_forall_facts
                .insert(key, vec![(or_fact.clone(), forall_params_and_dom)]);
        }
        Ok(())
    }

    fn store_a_fact_in_forall_fact(
        &mut self,
        fact: &ExistOrAndChainAtomicFact,
        forall_params_and_dom: Rc<KnownForallFactParamsAndDom>,
    ) -> Result<(), StoreFactError> {
        match fact {
            ExistOrAndChainAtomicFact::AtomicFact(spec_fact) => {
                self.store_atomic_fact_in_forall_fact(&spec_fact, forall_params_and_dom)
            }
            ExistOrAndChainAtomicFact::OrFact(or_fact) => {
                self.store_or_fact_in_forall_fact(&or_fact, forall_params_and_dom)
            }
            ExistOrAndChainAtomicFact::AndFact(and_fact) => {
                self.store_and_fact_in_forall_fact(&and_fact, forall_params_and_dom)
            }
            ExistOrAndChainAtomicFact::ChainFact(chain_fact) => {
                self.store_chain_fact_in_forall_fact(&chain_fact, forall_params_and_dom)
            }
            ExistOrAndChainAtomicFact::ExistFact(exist_fact) => {
                self.store_exist_fact_in_forall_fact(&exist_fact, forall_params_and_dom)
            }
        }
    }

    fn store_chain_fact_in_forall_fact(
        &mut self,
        chain_fact: &ChainFact,
        forall_params_and_dom: Rc<KnownForallFactParamsAndDom>,
    ) -> Result<(), StoreFactError> {
        for fact in chain_fact.facts()?.iter() {
            self.store_a_fact_in_forall_fact(
                &ExistOrAndChainAtomicFact::AtomicFact(fact.clone()),
                forall_params_and_dom.clone(),
            )?;
        }
        Ok(())
    }

    fn store_exist_fact_in_forall_fact(
        &mut self,
        exist_fact: &ExistFact,
        forall_params_and_dom: Rc<KnownForallFactParamsAndDom>,
    ) -> Result<(), StoreFactError> {
        let key = exist_fact.key();
        if let Some(vec_ref) = self.known_exist_facts_in_forall_facts.get_mut(&key) {
            vec_ref.push((exist_fact.clone(), forall_params_and_dom));
        } else {
            self.known_exist_facts_in_forall_facts
                .insert(key, vec![(exist_fact.clone(), forall_params_and_dom)]);
        }
        Ok(())
    }

    fn store_and_fact_in_forall_fact(
        &mut self,
        and_fact: &AndFact,
        forall_params_and_dom: Rc<KnownForallFactParamsAndDom>,
    ) -> Result<(), StoreFactError> {
        for fact in and_fact.facts.iter() {
            self.store_a_fact_in_forall_fact(
                &ExistOrAndChainAtomicFact::AtomicFact(fact.clone()),
                forall_params_and_dom.clone(),
            )?;
        }
        Ok(())
    }

    fn store_forall_fact(&mut self, forall_fact: Rc<ForallFact>) -> Result<(), StoreFactError> {
        let forall_params_and_dom = Rc::new(KnownForallFactParamsAndDom::new(
            forall_fact.params_def_with_type.clone(),
            forall_fact.dom_facts.clone(),
            forall_fact.line_file,
        ));

        for fact in forall_fact.then_facts.iter() {
            self.store_a_fact_in_forall_fact(fact, forall_params_and_dom.clone())?;
        }
        Ok(())
    }

    fn store_and_fact_by_ref(&mut self, and_fact: &AndFact) -> Result<(), StoreFactError> {
        for fact in and_fact.facts.iter() {
            self.store_atomic_fact(fact.clone())?;
        }
        Ok(())
    }

    fn store_and_fact(&mut self, and_fact: AndFact) -> Result<(), StoreFactError> {
        self.store_and_fact_by_ref(&and_fact)
    }

    fn store_forall_fact_with_iff(
        &mut self,
        forall_fact_with_iff: ForallFactWithIff,
    ) -> Result<(), StoreFactError> {
        let (forall_then_implies_iff, forall_iff_implies_then) =
            forall_fact_with_iff.to_two_forall_facts();
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
            Fact::ForallFactWithIff(forall_fact_with_iff) => {
                self.store_forall_fact_with_iff(forall_fact_with_iff)
            }
        }
    }

    /// Stores a fact without moving it; clones only where the underlying maps need owned values.
    pub fn store_fact_by_ref(&mut self, fact: &Fact) -> Result<(), StoreFactError> {
        match fact {
            Fact::AtomicFact(atomic_fact) => self.store_atomic_fact(atomic_fact.clone()),
            Fact::ExistFact(exist_fact) => self.store_exist_fact(exist_fact.clone()),
            Fact::OrFact(or_fact) => self.store_or_fact(or_fact.clone()),
            Fact::AndFact(and_fact) => self.store_and_fact_by_ref(and_fact),
            Fact::ChainFact(chain_fact) => self.store_chain_fact_by_ref(chain_fact),
            Fact::ForallFact(forall_fact) => self.store_forall_fact(Rc::new(forall_fact.clone())),
            Fact::ForallFactWithIff(forall_fact_with_iff) => {
                self.store_forall_fact_with_iff(forall_fact_with_iff.clone())
            }
        }
    }

    pub fn store_exist_or_and_chain_atomic_fact(
        &mut self,
        fact: &ExistOrAndChainAtomicFact,
    ) -> Result<(), StoreFactError> {
        match fact {
            ExistOrAndChainAtomicFact::AtomicFact(atomic_fact) => {
                self.store_atomic_fact(atomic_fact.clone())
            }
            ExistOrAndChainAtomicFact::AndFact(and_fact) => self.store_and_fact_by_ref(and_fact),
            ExistOrAndChainAtomicFact::ChainFact(chain_fact) => {
                self.store_chain_fact_by_ref(chain_fact)
            }
            ExistOrAndChainAtomicFact::OrFact(or_fact) => self.store_or_fact(or_fact.clone()),
            ExistOrAndChainAtomicFact::ExistFact(exist_fact) => {
                self.store_exist_fact(exist_fact.clone())
            }
        }
    }

    pub fn store_or_and_chain_atomic_fact(
        &mut self,
        fact: &OrAndChainAtomicFact,
    ) -> Result<(), StoreFactError> {
        match fact {
            OrAndChainAtomicFact::AtomicFact(atomic_fact) => {
                self.store_atomic_fact(atomic_fact.clone())
            }
            OrAndChainAtomicFact::AndFact(and_fact) => self.store_and_fact_by_ref(and_fact),
            OrAndChainAtomicFact::ChainFact(chain_fact) => self.store_chain_fact_by_ref(chain_fact),
            OrAndChainAtomicFact::OrFact(or_fact) => self.store_or_fact(or_fact.clone()),
        }
    }

    fn store_chain_fact_by_ref(&mut self, chain_fact: &ChainFact) -> Result<(), StoreFactError> {
        for fact in chain_fact.facts()?.iter() {
            self.store_atomic_fact(fact.clone())?;
        }
        Ok(())
    }

    fn store_chain_fact(&mut self, chain_fact: ChainFact) -> Result<(), StoreFactError> {
        self.store_chain_fact_by_ref(&chain_fact)
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
                // 1. Merge two equivalence classes: new vec = union of both, all keys pointing to either now point to new Rc.
                let merged: Vec<Obj> = {
                    let a: &Vec<Obj> = left_r.as_ref();
                    let b: &Vec<Obj> = right_r.as_ref();
                    let mut v: Vec<Obj> = a.iter().chain(b.iter()).cloned().collect();
                    v.sort_by(|a, b| a.to_string().cmp(&b.to_string()));
                    v.dedup_by(|a, b| a.to_string() == b.to_string());
                    v
                };
                let new_rc = Rc::new(merged);
                for obj in new_rc.iter() {
                    self.known_equality
                        .insert(obj.to_string(), Rc::clone(&new_rc));
                }
            }
            (Some(ref rc), None) => {
                // 2. Right not in any class: add right to left's class (Rc<Vec> is immutable, build new Vec and update all keys pointing to it).
                let mut new_vec = (**rc).clone();
                new_vec.push(equality.right.clone());
                let new_rc = Rc::new(new_vec);
                let keys_to_update: Vec<String> = self
                    .known_equality
                    .iter()
                    .filter(|(_, v)| Rc::ptr_eq(v, rc))
                    .map(|(k, _)| k.clone())
                    .collect();
                for k in keys_to_update {
                    self.known_equality.insert(k, Rc::clone(&new_rc));
                }
                self.known_equality.insert(right_as_string, new_rc);
            }
            (None, Some(ref rc)) => {
                // 2. Left not in any class: add left to right's class.
                let mut new_vec = (**rc).clone();
                new_vec.push(equality.left.clone());
                let new_rc = Rc::new(new_vec);
                let keys_to_update: Vec<String> = self
                    .known_equality
                    .iter()
                    .filter(|(_, v)| Rc::ptr_eq(v, rc))
                    .map(|(k, _)| k.clone())
                    .collect();
                for k in keys_to_update {
                    self.known_equality.insert(k, Rc::clone(&new_rc));
                }
                self.known_equality.insert(left_as_string, new_rc);
            }
            (None, None) => {
                // 3. Neither in any class: new equivalence class [left, right].
                let vec = vec![equality.left.clone(), equality.right.clone()];
                let new_rc = Rc::new(vec);
                self.known_equality
                    .insert(left_as_string.clone(), Rc::clone(&new_rc));
                self.known_equality.insert(right_as_string, new_rc);
            }
        }
        Ok(())
    }
}

impl Environment {
    pub fn new_empty_env() -> Self {
        Environment::new(
            HashMap::new(),
            HashMap::new(),
            HashMap::new(),
            HashMap::new(),
            HashMap::new(),
            HashMap::new(),
            HashMap::new(),
            HashMap::new(),
            HashMap::new(),
            HashMap::new(),
            HashMap::new(),
            HashMap::new(),
            HashMap::new(),
            HashMap::new(),
            HashMap::new(),
            HashMap::new(),
            HashMap::new(),
            HashMap::new(),
            HashMap::new(),
            HashMap::new(),
            HashMap::new(),
            HashMap::new(),
        )
    }
}

impl Environment {
    pub fn store_fact_to_cache_known_fact(
        &mut self,
        fact_key: String,
        fact_line_file: (usize, usize),
    ) -> Result<(), StoreFactError> {
        self.cache_known_fact.insert(fact_key, fact_line_file);
        Ok(())
    }
}

pub struct KnownForallFactParamsAndDom {
    pub params_def: Vec<ParamDefWithParamType>,
    pub dom: Vec<ExistOrAndChainAtomicFact>,
    pub line_file: (usize, usize),
}

impl KnownForallFactParamsAndDom {
    pub fn new(
        params: Vec<ParamDefWithParamType>,
        dom: Vec<ExistOrAndChainAtomicFact>,
        line_file: (usize, usize),
    ) -> Self {
        KnownForallFactParamsAndDom {
            params_def: params,
            dom,
            line_file,
        }
    }
}
