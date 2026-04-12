use crate::prelude::*;
use std::collections::HashMap;
use std::fmt;
use std::rc::Rc;

pub struct Environment {
    pub defined_identifiers: HashMap<IdentifierName, ()>,
    pub defined_def_props: HashMap<PropName, DefPropStmt>,
    pub defined_abstract_props: HashMap<AbstractPropName, DefAbstractPropStmt>,
    pub defined_structs: HashMap<StructName, DefStructStmt>,
    pub defined_families: HashMap<FamilyName, DefFamilyStmt>,
    pub defined_algorithms: HashMap<AlgoName, DefAlgoStmt>,

    pub known_equality: HashMap<ObjString, (HashMap<ObjString, AtomicFact>, Rc<Vec<Obj>>)>,

    pub known_atomic_facts_with_0_or_more_than_2_args:
        HashMap<(AtomicFactKey, bool), Vec<AtomicFact>>,
    pub known_atomic_facts_with_1_arg:
        HashMap<(AtomicFactKey, bool), HashMap<ObjString, AtomicFact>>,
    pub known_atomic_facts_with_2_args:
        HashMap<(AtomicFactKey, bool), HashMap<(ObjString, ObjString), AtomicFact>>,

    pub known_exist_facts: HashMap<ExistFactKey, Vec<ExistFact>>,
    pub known_or_facts: HashMap<OrFactKey, Vec<OrFact>>,

    pub known_atomic_facts_in_forall_facts:
        HashMap<(AtomicFactKey, bool), Vec<(AtomicFact, Rc<KnownForallFactParamsAndDom>)>>,
    pub known_exist_facts_in_forall_facts:
        HashMap<ExistFactKey, Vec<(ExistFact, Rc<KnownForallFactParamsAndDom>)>>,
    pub known_or_facts_in_forall_facts:
        HashMap<OrFactKey, Vec<(OrFact, Rc<KnownForallFactParamsAndDom>)>>,

    pub known_objs_equal_to_tuple: HashMap<ObjString, (Option<Tuple>, Option<Cart>, LineFile)>,
    pub known_objs_equal_to_cart: HashMap<ObjString, (Cart, LineFile)>,
    pub known_objs_equal_to_normalized_decimal_number: HashMap<ObjString, Number>,

    pub known_identifier_satisfy_struct: HashMap<FieldAccessName, StructObj>,

    pub known_objs_in_fn_sets: HashMap<ObjString, FnSet>,

    pub cache_well_defined_obj: HashMap<ObjString, ()>,
    pub cache_known_fact: HashMap<FactString, LineFile>,
}

impl Environment {
    pub fn new(
        objs: HashMap<IdentifierName, ()>,
        def_props: HashMap<PropName, DefPropStmt>,
        struct_defs: HashMap<StructName, DefStructStmt>,
        families: HashMap<FamilyName, DefFamilyStmt>,
        abstract_props: HashMap<AbstractPropName, DefAbstractPropStmt>,
        algorithms: HashMap<AlgoName, DefAlgoStmt>,
        field_access_name: HashMap<FieldAccessName, StructObj>,
        known_equality: HashMap<ObjString, (HashMap<ObjString, AtomicFact>, Rc<Vec<Obj>>)>,
        known_fn_in_fn_set: HashMap<ObjString, FnSet>,
        known_atomic_facts_with_0_or_more_than_2_args: HashMap<
            (AtomicFactKey, bool),
            Vec<AtomicFact>,
        >,
        known_atomic_facts_with_1_arg: HashMap<
            (AtomicFactKey, bool),
            HashMap<ObjString, AtomicFact>,
        >,
        known_atomic_facts_with_2_args: HashMap<
            (AtomicFactKey, bool),
            HashMap<(ObjString, ObjString), AtomicFact>,
        >,
        known_exist_facts: HashMap<ExistFactKey, Vec<ExistFact>>,
        known_atomic_facts_in_forall_facts: HashMap<
            (AtomicFactKey, bool),
            Vec<(AtomicFact, Rc<KnownForallFactParamsAndDom>)>,
        >,
        known_exist_facts_in_forall_facts: HashMap<
            ExistFactKey,
            Vec<(ExistFact, Rc<KnownForallFactParamsAndDom>)>,
        >,
        known_or_facts: HashMap<OrFactKey, Vec<OrFact>>,
        known_or_facts_in_forall_facts: HashMap<
            OrFactKey,
            Vec<(OrFact, Rc<KnownForallFactParamsAndDom>)>,
        >,
        known_tuple_objs: HashMap<ObjString, (Option<Tuple>, Option<Cart>, LineFile)>,
        known_cart_objs: HashMap<ObjString, (Cart, LineFile)>,
        known_calculated_value_of_obj: HashMap<ObjString, Number>,
        cache_known_valid_obj: HashMap<ObjString, ()>,
        cache_known_fact: HashMap<FactString, LineFile>,
    ) -> Self {
        Environment {
            defined_identifiers: objs,
            defined_def_props: def_props,
            defined_structs: struct_defs,
            defined_families: families,
            defined_abstract_props: abstract_props,
            defined_algorithms: algorithms,
            known_identifier_satisfy_struct: field_access_name,
            known_equality,
            known_objs_in_fn_sets: known_fn_in_fn_set,
            known_atomic_facts_with_0_or_more_than_2_args,
            known_atomic_facts_with_1_arg: known_atomic_facts_with_1_arg,
            known_atomic_facts_with_2_args: known_atomic_facts_with_2_args,
            known_exist_facts,
            known_atomic_facts_in_forall_facts,
            known_exist_facts_in_forall_facts,
            known_or_facts,
            known_or_facts_in_forall_facts,
            known_objs_equal_to_tuple: known_tuple_objs,
            known_objs_equal_to_cart: known_cart_objs,
            known_objs_equal_to_normalized_decimal_number: known_calculated_value_of_obj,
            cache_well_defined_obj: cache_known_valid_obj,
            cache_known_fact,
        }
    }
}

impl fmt::Display for Environment {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Environment {{\n")?;
        write!(f, "    objs: {:?}\n", self.defined_identifiers.len())?;
        write!(f, "    def_props: {:?}\n", self.defined_def_props.len())?;
        write!(f, "    defined_structs: {:?}\n", self.defined_structs.len())?;
        write!(f, "    families: {:?}\n", self.defined_families.len())?;
        write!(f, "    algorithms: {:?}\n", self.defined_algorithms.len())?;
        write!(f, "    known_equality: {:?}\n", self.known_equality.len())?;
        write!(
            f,
            "    known_fn_in_fn_set: {:?}\n",
            self.known_objs_in_fn_sets.len()
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
    pub fn store_atomic_fact_by_ref(
        &mut self,
        atomic_fact: &AtomicFact,
    ) -> Result<(), RuntimeErrorStruct> {
        self.store_atomic_fact(atomic_fact.clone())
    }

    pub(crate) fn store_atomic_fact(
        &mut self,
        atomic_fact: AtomicFact,
    ) -> Result<(), RuntimeErrorStruct> {
        match atomic_fact {
            AtomicFact::EqualFact(equal_fact) => self.store_equality(&equal_fact),
            _ => {
                let key: AtomicFactKey = atomic_fact.key();
                let is_true = atomic_fact.is_true();
                if atomic_fact.args().len() == 1 {
                    let arg_key: ObjString = atomic_fact.args()[0].to_string();
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
                    let arg_key1: ObjString = atomic_fact.args()[0].to_string();
                    let arg_key2: ObjString = atomic_fact.args()[1].to_string();
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

    fn store_exist_fact(&mut self, exist_fact: ExistFact) -> Result<(), RuntimeErrorStruct> {
        let key: ExistFactKey = exist_fact.key();
        if let Some(vec_ref) = self.known_exist_facts.get_mut(&key) {
            vec_ref.push(exist_fact);
        } else {
            self.known_exist_facts.insert(key, vec![exist_fact]);
        }
        Ok(())
    }

    fn store_or_fact(&mut self, or_fact: OrFact) -> Result<(), RuntimeErrorStruct> {
        let key: OrFactKey = or_fact.key();
        if let Some(vec_ref) = self.known_or_facts.get_mut(&key) {
            vec_ref.push(or_fact);
        } else {
            self.known_or_facts.insert(key, vec![or_fact]);
        }
        Ok(())
    }

    fn store_atomic_fact_in_forall_fact(
        &mut self,
        atomic_fact: AtomicFact,
        forall_params_and_dom: Rc<KnownForallFactParamsAndDom>,
    ) -> Result<(), RuntimeErrorStruct> {
        let key: AtomicFactKey = atomic_fact.key();
        let is_true = atomic_fact.is_true();
        if let Some(vec_ref) = self
            .known_atomic_facts_in_forall_facts
            .get_mut(&(key.clone(), is_true))
        {
            vec_ref.push((atomic_fact, forall_params_and_dom));
        } else {
            self.known_atomic_facts_in_forall_facts
                .insert((key, is_true), vec![(atomic_fact, forall_params_and_dom)]);
        }
        Ok(())
    }

    fn store_or_fact_in_forall_fact(
        &mut self,
        or_fact: &OrFact,
        forall_params_and_dom: Rc<KnownForallFactParamsAndDom>,
    ) -> Result<(), RuntimeErrorStruct> {
        let key: OrFactKey = or_fact.key();
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
    ) -> Result<(), RuntimeErrorStruct> {
        match fact {
            ExistOrAndChainAtomicFact::AtomicFact(spec_fact) => {
                self.store_atomic_fact_in_forall_fact(spec_fact.clone(), forall_params_and_dom)
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
    ) -> Result<(), RuntimeErrorStruct> {
        for fact in chain_fact
            .facts()
            .map_err(|e| {
                RuntimeErrorStruct::new_with_conflict(
                    e.statement.clone(),
                    e.msg.clone(),
                    e.line_file.clone(),
                    e.conflict_with.clone(),
                    Some(NewAtomicFactRuntimeError(e).into()),
                    vec![],
                )
            })?
            .into_iter()
        {
            self.store_atomic_fact_in_forall_fact(fact, forall_params_and_dom.clone())?;
        }
        Ok(())
    }

    fn store_exist_fact_in_forall_fact(
        &mut self,
        exist_fact: &ExistFact,
        forall_params_and_dom: Rc<KnownForallFactParamsAndDom>,
    ) -> Result<(), RuntimeErrorStruct> {
        let key: ExistFactKey = exist_fact.key();
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
    ) -> Result<(), RuntimeErrorStruct> {
        for fact in and_fact.facts.iter() {
            self.store_atomic_fact_in_forall_fact(fact.clone(), forall_params_and_dom.clone())?;
        }
        Ok(())
    }

    fn store_forall_fact(&mut self, forall_fact: Rc<ForallFact>) -> Result<(), RuntimeErrorStruct> {
        let forall_params_and_dom = Rc::new(KnownForallFactParamsAndDom::new(
            forall_fact.params_def_with_type.clone(),
            forall_fact.dom_facts.clone(),
            forall_fact.line_file.clone(),
        ));

        for fact in forall_fact.then_facts.iter() {
            self.store_a_fact_in_forall_fact(fact, forall_params_and_dom.clone())?;
        }
        Ok(())
    }

    fn store_and_fact(&mut self, and_fact: AndFact) -> Result<(), RuntimeErrorStruct> {
        for atomic_fact in and_fact.facts {
            self.store_atomic_fact(atomic_fact)?;
        }
        Ok(())
    }

    fn store_forall_fact_with_iff(
        &mut self,
        forall_fact_with_iff: ForallFactWithIff,
    ) -> Result<(), RuntimeErrorStruct> {
        let (forall_then_implies_iff, forall_iff_implies_then) =
            forall_fact_with_iff.to_two_forall_facts();
        self.store_forall_fact(Rc::new(forall_then_implies_iff))?;
        self.store_forall_fact(Rc::new(forall_iff_implies_then))?;
        Ok(())
    }

    pub fn store_fact(&mut self, fact: Fact) -> Result<(), RuntimeErrorStruct> {
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

    pub fn store_exist_fact_by_ref(
        &mut self,
        exist_fact: &ExistFact,
    ) -> Result<(), RuntimeErrorStruct> {
        self.store_exist_fact(exist_fact.clone())
    }

    pub fn store_exist_or_and_chain_atomic_fact(
        &mut self,
        fact: ExistOrAndChainAtomicFact,
    ) -> Result<(), RuntimeErrorStruct> {
        match fact {
            ExistOrAndChainAtomicFact::AtomicFact(atomic_fact) => {
                self.store_atomic_fact(atomic_fact)
            }
            ExistOrAndChainAtomicFact::AndFact(and_fact) => self.store_and_fact(and_fact),
            ExistOrAndChainAtomicFact::ChainFact(chain_fact) => self.store_chain_fact(chain_fact),
            ExistOrAndChainAtomicFact::OrFact(or_fact) => self.store_or_fact(or_fact),
            ExistOrAndChainAtomicFact::ExistFact(exist_fact) => self.store_exist_fact(exist_fact),
        }
    }

    pub fn store_and_chain_atomic_fact(
        &mut self,
        and_chain_atomic_fact: AndChainAtomicFact,
    ) -> Result<(), RuntimeErrorStruct> {
        match and_chain_atomic_fact {
            AndChainAtomicFact::AtomicFact(atomic_fact) => self.store_atomic_fact(atomic_fact),
            AndChainAtomicFact::AndFact(and_fact) => self.store_and_fact(and_fact),
            AndChainAtomicFact::ChainFact(chain_fact) => self.store_chain_fact(chain_fact),
        }
    }

    pub fn store_or_and_chain_atomic_fact(
        &mut self,
        fact: OrAndChainAtomicFact,
    ) -> Result<(), RuntimeErrorStruct> {
        match fact {
            OrAndChainAtomicFact::AtomicFact(atomic_fact) => self.store_atomic_fact(atomic_fact),
            OrAndChainAtomicFact::AndFact(and_fact) => self.store_and_fact(and_fact),
            OrAndChainAtomicFact::ChainFact(chain_fact) => self.store_chain_fact(chain_fact),
            OrAndChainAtomicFact::OrFact(or_fact) => self.store_or_fact(or_fact),
        }
    }

    fn store_chain_fact(&mut self, chain_fact: ChainFact) -> Result<(), RuntimeErrorStruct> {
        let atomic_facts = chain_fact
            .facts_with_order_transitive_closure()
            .map_err(|e| {
                RuntimeErrorStruct::new_with_conflict(
                    e.statement.clone(),
                    e.msg.clone(),
                    e.line_file.clone(),
                    e.conflict_with.clone(),
                    Some(NewAtomicFactRuntimeError(e).into()),
                    vec![],
                )
            })?;
        for atomic_fact in atomic_facts {
            self.store_atomic_fact(atomic_fact)?;
        }
        Ok(())
    }

    pub fn store_chain_fact_by_ref(
        &mut self,
        chain_fact: &ChainFact,
    ) -> Result<(), RuntimeErrorStruct> {
        self.store_chain_fact(chain_fact.clone())
    }

    pub fn store_equality(&mut self, equality: &EqualFact) -> Result<(), RuntimeErrorStruct> {
        let left_as_string: ObjString = equality.left.to_string();
        let right_as_string: ObjString = equality.right.to_string();
        if left_as_string == right_as_string {
            return Ok(());
        }

        let left_rc = self
            .known_equality
            .get(&left_as_string)
            .map(|(_, rc)| Rc::clone(rc));
        let right_rc = self
            .known_equality
            .get(&right_as_string)
            .map(|(_, rc)| Rc::clone(rc));

        let equal_atomic_fact = AtomicFact::EqualFact(equality.clone());

        match (left_rc, right_rc) {
            (Some(ref left_class_rc), Some(ref right_class_rc)) => {
                if Rc::ptr_eq(left_class_rc, right_class_rc) {
                    return Ok(());
                }
                let merged_vec: Vec<Obj> = {
                    let left_vec: &Vec<Obj> = left_class_rc.as_ref();
                    let right_vec: &Vec<Obj> = right_class_rc.as_ref();
                    let mut merged = Vec::with_capacity(left_vec.len() + right_vec.len());
                    for obj in left_vec.iter().chain(right_vec.iter()) {
                        merged.push(obj.clone());
                    }
                    merged.sort_by(|a_obj, b_obj| a_obj.to_string().cmp(&b_obj.to_string()));
                    merged.dedup_by(|a_obj, b_obj| a_obj.to_string() == b_obj.to_string());
                    merged
                };
                let new_equiv_rc = Rc::new(merged_vec);

                let keys_in_either_class: Vec<ObjString> = self
                    .known_equality
                    .iter()
                    .filter(|(_, (_, class_rc))| {
                        Rc::ptr_eq(class_rc, left_class_rc) || Rc::ptr_eq(class_rc, right_class_rc)
                    })
                    .map(|(k, _)| k.clone())
                    .collect();

                for key_in_class in keys_in_either_class {
                    let removed_entry = match self.known_equality.remove(&key_in_class) {
                        Some(entry) => entry,
                        None => continue,
                    };
                    let (mut direct_equality_proof_map, _) = removed_entry;
                    if key_in_class == left_as_string {
                        direct_equality_proof_map
                            .insert(right_as_string.clone(), equal_atomic_fact.clone());
                    }
                    if key_in_class == right_as_string {
                        direct_equality_proof_map
                            .insert(left_as_string.clone(), equal_atomic_fact.clone());
                    }
                    self.known_equality.insert(
                        key_in_class,
                        (direct_equality_proof_map, Rc::clone(&new_equiv_rc)),
                    );
                }
            }
            (Some(existing_class_rc), None) => {
                let mut new_vec = (*existing_class_rc).clone();
                new_vec.push(equality.right.clone());
                let new_equiv_rc = Rc::new(new_vec);

                let keys_in_existing_class: Vec<ObjString> = self
                    .known_equality
                    .iter()
                    .filter(|(_, (_, class_rc))| Rc::ptr_eq(class_rc, &existing_class_rc))
                    .map(|(k, _)| k.clone())
                    .collect();

                for key_in_class in keys_in_existing_class {
                    let removed_entry = match self.known_equality.remove(&key_in_class) {
                        Some(entry) => entry,
                        None => continue,
                    };
                    let (mut direct_equality_proof_map, _) = removed_entry;
                    if key_in_class == left_as_string {
                        direct_equality_proof_map
                            .insert(right_as_string.clone(), equal_atomic_fact.clone());
                    }
                    self.known_equality.insert(
                        key_in_class,
                        (direct_equality_proof_map, Rc::clone(&new_equiv_rc)),
                    );
                }

                let mut proof_for_new_right: HashMap<ObjString, AtomicFact> = HashMap::new();
                proof_for_new_right.insert(left_as_string.clone(), equal_atomic_fact.clone());
                self.known_equality
                    .insert(right_as_string, (proof_for_new_right, new_equiv_rc));
            }
            (None, Some(existing_class_rc)) => {
                let mut new_vec = (*existing_class_rc).clone();
                new_vec.push(equality.left.clone());
                let new_equiv_rc = Rc::new(new_vec);

                let keys_in_existing_class: Vec<ObjString> = self
                    .known_equality
                    .iter()
                    .filter(|(_, (_, class_rc))| Rc::ptr_eq(class_rc, &existing_class_rc))
                    .map(|(k, _)| k.clone())
                    .collect();

                for key_in_class in keys_in_existing_class {
                    let removed_entry = match self.known_equality.remove(&key_in_class) {
                        Some(entry) => entry,
                        None => continue,
                    };
                    let (mut direct_equality_proof_map, _) = removed_entry;
                    if key_in_class == right_as_string {
                        direct_equality_proof_map
                            .insert(left_as_string.clone(), equal_atomic_fact.clone());
                    }
                    self.known_equality.insert(
                        key_in_class,
                        (direct_equality_proof_map, Rc::clone(&new_equiv_rc)),
                    );
                }

                let mut proof_for_new_left: HashMap<ObjString, AtomicFact> = HashMap::new();
                proof_for_new_left.insert(right_as_string.clone(), equal_atomic_fact.clone());
                self.known_equality
                    .insert(left_as_string, (proof_for_new_left, new_equiv_rc));
            }
            (None, None) => {
                let equiv_members = vec![equality.left.clone(), equality.right.clone()];
                let new_equiv_rc = Rc::new(equiv_members);

                let mut left_direct_proof_map: HashMap<ObjString, AtomicFact> = HashMap::new();
                left_direct_proof_map.insert(right_as_string.clone(), equal_atomic_fact.clone());

                let mut right_direct_proof_map: HashMap<ObjString, AtomicFact> = HashMap::new();
                right_direct_proof_map.insert(left_as_string.clone(), equal_atomic_fact);

                self.known_equality.insert(
                    left_as_string.clone(),
                    (left_direct_proof_map, Rc::clone(&new_equiv_rc)),
                );
                self.known_equality
                    .insert(right_as_string, (right_direct_proof_map, new_equiv_rc));
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
        fact_key: FactString,
        fact_line_file: LineFile,
    ) -> Result<(), RuntimeErrorStruct> {
        self.cache_known_fact.insert(fact_key, fact_line_file);
        Ok(())
    }
}

pub struct KnownForallFactParamsAndDom {
    pub params_def: Vec<ParamGroupWithParamType>,
    pub dom: Vec<ExistOrAndChainAtomicFact>,
    pub line_file: LineFile,
}

impl KnownForallFactParamsAndDom {
    pub fn new(
        params: Vec<ParamGroupWithParamType>,
        dom: Vec<ExistOrAndChainAtomicFact>,
        line_file: LineFile,
    ) -> Self {
        KnownForallFactParamsAndDom {
            params_def: params,
            dom,
            line_file,
        }
    }
}
