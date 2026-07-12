use super::known_fn::KnownFnInfo;
use crate::prelude::*;
use std::collections::HashMap;
use std::fmt;
use std::rc::Rc;

pub type AtomicFactInForallArgShapeKey = Vec<(ObjKind, ObjOperatorString)>;
pub type AtomicFactInForallArgShapeIndex = HashMap<
    (AtomicFactKey, bool),
    HashMap<AtomicFactInForallArgShapeKey, Vec<(AtomicFact, Rc<KnownForallFactParamsAndDom>)>>,
>;

/// The mutable mathematical context for a runtime environment.
///
/// `Environment` is intentionally broad: it is the physical storage for the
/// checked world that later statements can reuse. The fields are grouped by
/// role rather than by proof rule:
///
/// - definition tables for identifiers, predicates, algorithms, structs,
///   templates, theorems, and strategies;
/// - known fact indexes for equality, atomic, existential, and disjunctive
///   facts;
/// - known `forall` indexes, including argument-shape indexes for faster
///   matching against later goals;
/// - derived object-shape caches for tuples, carts, finite sequences,
///   matrices, object values, set builders, and function-set information;
/// - verification caches for well-defined objects and already-known facts;
/// - strategy registrations and stopped-strategy state.
#[derive(Clone)]
pub struct Environment {
    pub defined_identifiers: HashMap<IdentifierName, ParamObjType>,
    pub defined_def_props: HashMap<PropName, DefPropStmt>,
    pub defined_abstract_props: HashMap<AbstractPropName, DefAbstractPropStmt>,
    pub defined_algorithms: HashMap<AlgoName, DefAlgoStmt>,
    pub defined_structs: HashMap<StructName, DefStructStmt>,
    pub defined_templates: HashMap<TemplateName, DefTemplateStmt>,
    pub defined_thm_stmts: HashMap<ThmName, DefThmStmt>,
    pub defined_thm_trust_summaries: HashMap<ThmName, ProofTrustSummary>,
    pub defined_strategy_stmts: HashMap<StrategyName, DefStrategyStmt>,

    pub known_equality: HashMap<ObjString, (HashMap<ObjString, AtomicFact>, Rc<Vec<Obj>>)>,

    pub known_atomic_facts_with_0_or_more_than_2_args:
        HashMap<(AtomicFactKey, bool), Vec<AtomicFact>>,
    pub known_atomic_facts_with_1_arg:
        HashMap<(AtomicFactKey, bool), HashMap<ObjString, AtomicFact>>,
    pub known_atomic_facts_with_2_args:
        HashMap<(AtomicFactKey, bool), HashMap<(ObjString, ObjString), AtomicFact>>,

    pub known_exist_facts: HashMap<ExistFactKey, Vec<ExistFactEnum>>,
    pub known_or_facts: HashMap<OrFactKey, Vec<OrFact>>,

    pub known_atomic_facts_in_forall_facts:
        HashMap<(AtomicFactKey, bool), Vec<(AtomicFact, Rc<KnownForallFactParamsAndDom>)>>,
    pub known_atomic_facts_in_forall_facts_by_arg_shape: AtomicFactInForallArgShapeIndex,
    pub known_exist_facts_in_forall_facts:
        HashMap<ExistFactKey, Vec<(ExistFactEnum, Rc<KnownForallFactParamsAndDom>)>>,
    pub known_and_facts_in_forall_facts:
        HashMap<AndFactKey, Vec<(AndFact, Rc<KnownForallFactParamsAndDom>)>>,
    pub known_or_facts_in_forall_facts:
        HashMap<OrFactKey, Vec<(OrFact, Rc<KnownForallFactParamsAndDom>)>>,

    pub known_objs_equal_to_tuple: HashMap<ObjString, (Option<Tuple>, Option<Cart>, LineFile)>,
    pub known_objs_equal_to_cart: HashMap<ObjString, (Cart, LineFile)>,
    pub known_objs_equal_to_finite_seq_list:
        HashMap<ObjString, (FiniteSeqListObj, Option<FiniteSeqSet>, LineFile)>,
    pub known_objs_equal_to_matrix_list:
        HashMap<ObjString, (MatrixListObj, Option<MatrixSet>, LineFile)>,
    pub known_obj_values: HashMap<ObjString, KnownObjValue>,
    pub known_objs_equal_to_set_builder: HashMap<ObjString, (SetBuilder, LineFile)>,

    pub known_objs_in_fn_sets: HashMap<ObjString, KnownFnInfo>,

    pub known_transitive_props: HashMap<String, ()>,
    pub known_symmetric_props: HashMap<String, SymmetricPropValue>,
    pub known_reflexive_props: HashMap<String, ()>,
    pub known_antisymmetric_props: HashMap<String, ()>,

    pub cache_well_defined_obj: HashMap<ObjString, ()>,
    pub cache_known_fact: HashMap<FactString, LineFile>,
    pub cache_known_fact_trust: HashMap<FactString, ProofTrustSummary>,

    pub used_strategy_stmts: HashMap<(PropName, bool), StrategyName>,
    pub stopped_strategy_stmts: HashMap<(PropName, bool), StrategyName>,
}

#[derive(Clone)]
pub enum KnownObjValue {
    SimplifiedNumber(Number), // when a = 1.0, store a = 1
    SimplifiedFraction(Div),  // when a = 1/3, store a = 1/3
}

impl Environment {
    pub fn new(
        objs: HashMap<IdentifierName, ParamObjType>,
        def_props: HashMap<PropName, DefPropStmt>,
        abstract_props: HashMap<AbstractPropName, DefAbstractPropStmt>,
        algorithms: HashMap<AlgoName, DefAlgoStmt>,
        structs: HashMap<StructName, DefStructStmt>,
        templates: HashMap<TemplateName, DefTemplateStmt>,
        defined_thm_stmts: HashMap<ThmName, DefThmStmt>,
        defined_thm_trust_summaries: HashMap<ThmName, ProofTrustSummary>,
        known_equality: HashMap<ObjString, (HashMap<ObjString, AtomicFact>, Rc<Vec<Obj>>)>,
        known_fn_in_fn_set: HashMap<ObjString, KnownFnInfo>,
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
        known_exist_facts: HashMap<ExistFactKey, Vec<ExistFactEnum>>,
        known_atomic_facts_in_forall_facts: HashMap<
            (AtomicFactKey, bool),
            Vec<(AtomicFact, Rc<KnownForallFactParamsAndDom>)>,
        >,
        known_exist_facts_in_forall_facts: HashMap<
            ExistFactKey,
            Vec<(ExistFactEnum, Rc<KnownForallFactParamsAndDom>)>,
        >,
        known_and_facts_in_forall_facts: HashMap<
            AndFactKey,
            Vec<(AndFact, Rc<KnownForallFactParamsAndDom>)>,
        >,
        known_or_facts: HashMap<OrFactKey, Vec<OrFact>>,
        known_or_facts_in_forall_facts: HashMap<
            OrFactKey,
            Vec<(OrFact, Rc<KnownForallFactParamsAndDom>)>,
        >,
        known_tuple_objs: HashMap<ObjString, (Option<Tuple>, Option<Cart>, LineFile)>,
        known_cart_objs: HashMap<ObjString, (Cart, LineFile)>,
        known_finite_seq_list_objs: HashMap<
            ObjString,
            (FiniteSeqListObj, Option<FiniteSeqSet>, LineFile),
        >,
        known_matrix_list_objs: HashMap<ObjString, (MatrixListObj, Option<MatrixSet>, LineFile)>,
        known_obj_values: HashMap<ObjString, KnownObjValue>,
        known_set_builder_objs: HashMap<ObjString, (SetBuilder, LineFile)>,
        cache_known_valid_obj: HashMap<ObjString, ()>,
        cache_known_fact: HashMap<FactString, LineFile>,
        cache_known_fact_trust: HashMap<FactString, ProofTrustSummary>,
    ) -> Self {
        Environment {
            defined_identifiers: objs,
            defined_def_props: def_props,
            defined_abstract_props: abstract_props,
            defined_algorithms: algorithms,
            defined_structs: structs,
            defined_templates: templates,
            defined_thm_stmts,
            defined_thm_trust_summaries,
            defined_strategy_stmts: HashMap::new(),
            known_equality,
            known_objs_in_fn_sets: known_fn_in_fn_set,
            known_atomic_facts_with_0_or_more_than_2_args,
            known_atomic_facts_with_1_arg: known_atomic_facts_with_1_arg,
            known_atomic_facts_with_2_args: known_atomic_facts_with_2_args,
            known_exist_facts,
            known_atomic_facts_in_forall_facts,
            known_atomic_facts_in_forall_facts_by_arg_shape: HashMap::new(),
            known_exist_facts_in_forall_facts,
            known_and_facts_in_forall_facts,
            known_or_facts,
            known_or_facts_in_forall_facts,
            known_objs_equal_to_tuple: known_tuple_objs,
            known_objs_equal_to_cart: known_cart_objs,
            known_objs_equal_to_finite_seq_list: known_finite_seq_list_objs,
            known_objs_equal_to_matrix_list: known_matrix_list_objs,
            known_obj_values,
            known_objs_equal_to_set_builder: known_set_builder_objs,
            known_transitive_props: HashMap::new(),
            known_symmetric_props: HashMap::new(),
            known_reflexive_props: HashMap::new(),
            known_antisymmetric_props: HashMap::new(),
            cache_well_defined_obj: cache_known_valid_obj,
            cache_known_fact,
            cache_known_fact_trust,
            used_strategy_stmts: HashMap::new(),
            stopped_strategy_stmts: HashMap::new(),
        }
    }
}

impl fmt::Display for Environment {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Environment {{\n")?;
        write!(f, "    objs: {:?}\n", self.defined_identifiers.len())?;
        write!(f, "    def_props: {:?}\n", self.defined_def_props.len())?;
        write!(f, "    algorithms: {:?}\n", self.defined_algorithms.len())?;
        write!(f, "    structs: {:?}\n", self.defined_structs.len())?;
        write!(f, "    templates: {:?}\n", self.defined_templates.len())?;
        write!(f, "    known_equality: {:?}\n", self.known_equality.len())?;
        write!(
            f,
            "    known_fn_in_fn_set: {:?}\n",
            self.known_objs_in_fn_sets.len()
        )?;
        write!(
            f,
            "    known_transitive_props: {:?}\n",
            self.known_transitive_props.len()
        )?;
        write!(
            f,
            "    known_symmetric_props: {} predicates, {} permutations\n",
            self.known_symmetric_props.len(),
            self.known_symmetric_props
                .values()
                .map(|v| v.len())
                .sum::<usize>()
        )?;
        write!(
            f,
            "    known_reflexive_props: {:?}\n",
            self.known_reflexive_props.len()
        )?;
        write!(
            f,
            "    known_antisymmetric_props: {:?}\n",
            self.known_antisymmetric_props.len()
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
            "    known_atomic_facts_in_forall_facts_by_arg_shape: {:?}\n",
            self.known_atomic_facts_in_forall_facts_by_arg_shape.len()
        )?;
        write!(
            f,
            "    known_exist_facts_in_forall_facts: {:?}\n",
            self.known_exist_facts_in_forall_facts.len()
        )?;
        write!(
            f,
            "    known_and_facts_in_forall_facts: {:?}\n",
            self.known_and_facts_in_forall_facts.len()
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
    ) -> Result<(), RuntimeError> {
        self.store_atomic_fact(atomic_fact.clone())
    }

    pub fn store_atomic_fact(&mut self, atomic_fact: AtomicFact) -> Result<(), RuntimeError> {
        match atomic_fact {
            AtomicFact::EqualFact(equal_fact) => self.store_equality(&equal_fact),
            _ => {
                let key: AtomicFactKey = atomic_fact.key();
                let is_true = atomic_fact.is_true();
                let (arg_len, arg_key1, arg_key2) = {
                    let args = atomic_fact.args_ref();
                    let arg_key1 = args.first().map(|arg| arg.to_string());
                    let arg_key2 = args.get(1).map(|arg| arg.to_string());
                    (args.len(), arg_key1, arg_key2)
                };
                if arg_len == 1 {
                    let arg_key: ObjString = arg_key1.expect("one argument key should exist");
                    if let Some(map) = self
                        .known_atomic_facts_with_1_arg
                        .get_mut(&(key.clone(), is_true))
                    {
                        map.insert(arg_key, atomic_fact);
                    } else {
                        self.known_atomic_facts_with_1_arg
                            .insert((key, is_true), HashMap::from([(arg_key, atomic_fact)]));
                    }
                } else if arg_len == 2 {
                    let arg_key1: ObjString = arg_key1.expect("first argument key should exist");
                    let arg_key2: ObjString = arg_key2.expect("second argument key should exist");
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

    fn store_exist_fact(&mut self, exist_fact: ExistFactEnum) -> Result<(), RuntimeError> {
        let key: ExistFactKey = exist_fact.key();
        if let Some(vec_ref) = self.known_exist_facts.get_mut(&key) {
            vec_ref.push(exist_fact);
        } else {
            self.known_exist_facts.insert(key, vec![exist_fact]);
        }
        Ok(())
    }

    fn store_or_fact(&mut self, or_fact: OrFact) -> Result<(), RuntimeError> {
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
    ) -> Result<(), RuntimeError> {
        let key: AtomicFactKey = atomic_fact.key();
        let is_true = atomic_fact.is_true();

        if atomic_fact_has_top_level_fn_arg_head_with_forall_free_param(&atomic_fact) {
            let lookup_key = (key, is_true);
            if let Some(vec_ref) = self.known_atomic_facts_in_forall_facts.get_mut(&lookup_key) {
                vec_ref.push((atomic_fact, forall_params_and_dom));
            } else {
                self.known_atomic_facts_in_forall_facts
                    .insert(lookup_key, vec![(atomic_fact, forall_params_and_dom)]);
            }
            return Ok(());
        }

        let lookup_key = (key, is_true);
        let arg_shape_key = atomic_fact_in_forall_arg_shape_key(&atomic_fact);
        let arg_shape_map = self
            .known_atomic_facts_in_forall_facts_by_arg_shape
            .entry(lookup_key)
            .or_default();
        arg_shape_map
            .entry(arg_shape_key)
            .or_default()
            .push((atomic_fact, forall_params_and_dom));
        Ok(())
    }

    fn store_or_fact_in_forall_fact(
        &mut self,
        or_fact: &OrFact,
        forall_params_and_dom: Rc<KnownForallFactParamsAndDom>,
    ) -> Result<(), RuntimeError> {
        let key: OrFactKey = or_fact.key();
        if let Some(vec_ref) = self.known_or_facts_in_forall_facts.get_mut(&key) {
            vec_ref.push((or_fact.clone(), forall_params_and_dom));
        } else {
            self.known_or_facts_in_forall_facts
                .insert(key, vec![(or_fact.clone(), forall_params_and_dom)]);
        }
        Ok(())
    }

    fn store_whole_and_fact_in_forall_fact(
        &mut self,
        and_fact: &AndFact,
        forall_params_and_dom: Rc<KnownForallFactParamsAndDom>,
    ) -> Result<(), RuntimeError> {
        let key: AndFactKey = and_fact.key();
        if let Some(vec_ref) = self.known_and_facts_in_forall_facts.get_mut(&key) {
            vec_ref.push((and_fact.clone(), forall_params_and_dom));
        } else {
            self.known_and_facts_in_forall_facts
                .insert(key, vec![(and_fact.clone(), forall_params_and_dom)]);
        }
        Ok(())
    }

    fn store_a_fact_in_forall_fact(
        &mut self,
        fact: &ExistOrAndChainAtomicFact,
        forall_params_and_dom: Rc<KnownForallFactParamsAndDom>,
    ) -> Result<(), RuntimeError> {
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
    ) -> Result<(), RuntimeError> {
        for fact in chain_fact
            .facts()
            .map_err(RuntimeError::wrap_new_fact_as_store_conflict)?
            .into_iter()
        {
            self.store_atomic_fact_in_forall_fact(fact, forall_params_and_dom.clone())?;
        }
        Ok(())
    }

    fn store_exist_fact_in_forall_fact(
        &mut self,
        exist_fact: &ExistFactEnum,
        forall_params_and_dom: Rc<KnownForallFactParamsAndDom>,
    ) -> Result<(), RuntimeError> {
        let pair = || (exist_fact.clone(), forall_params_and_dom.clone());
        let key: ExistFactKey = exist_fact.key();
        if let Some(vec_ref) = self.known_exist_facts_in_forall_facts.get_mut(&key) {
            vec_ref.push(pair());
        } else {
            self.known_exist_facts_in_forall_facts
                .insert(key, vec![pair()]);
        }
        let alpha_key = exist_fact.alpha_normalized_key();
        if alpha_key != exist_fact.key() {
            if let Some(vec_ref) = self.known_exist_facts_in_forall_facts.get_mut(&alpha_key) {
                vec_ref.push(pair());
            } else {
                self.known_exist_facts_in_forall_facts
                    .insert(alpha_key, vec![pair()]);
            }
        }
        Ok(())
    }

    fn store_and_fact_in_forall_fact(
        &mut self,
        and_fact: &AndFact,
        forall_params_and_dom: Rc<KnownForallFactParamsAndDom>,
    ) -> Result<(), RuntimeError> {
        self.store_whole_and_fact_in_forall_fact(and_fact, forall_params_and_dom.clone())?;
        for fact in and_fact.facts.iter() {
            self.store_atomic_fact_in_forall_fact(fact.clone(), forall_params_and_dom.clone())?;
        }
        Ok(())
    }

    fn store_forall_fact(&mut self, forall_fact: Rc<ForallFact>) -> Result<(), RuntimeError> {
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

    fn store_and_fact(&mut self, and_fact: AndFact) -> Result<(), RuntimeError> {
        for atomic_fact in and_fact.facts {
            self.store_atomic_fact(atomic_fact)?;
        }
        Ok(())
    }

    fn store_forall_fact_with_iff(
        &mut self,
        forall_fact_with_iff: ForallFactWithIff,
    ) -> Result<(), RuntimeError> {
        let (forall_then_implies_iff, forall_iff_implies_then) =
            forall_fact_with_iff.to_two_forall_facts()?;
        self.store_forall_fact(Rc::new(forall_then_implies_iff))?;
        self.store_forall_fact(Rc::new(forall_iff_implies_then))?;
        Ok(())
    }

    pub fn store_fact(&mut self, fact: Fact) -> Result<(), RuntimeError> {
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
            Fact::NotForall(_) => Ok(()),
        }
    }

    pub fn store_exist_fact_by_ref(
        &mut self,
        exist_fact: &ExistFactEnum,
    ) -> Result<(), RuntimeError> {
        self.store_exist_fact(exist_fact.clone())
    }

    pub fn store_exist_or_and_chain_atomic_fact(
        &mut self,
        fact: ExistOrAndChainAtomicFact,
    ) -> Result<(), RuntimeError> {
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
    ) -> Result<(), RuntimeError> {
        match and_chain_atomic_fact {
            AndChainAtomicFact::AtomicFact(atomic_fact) => self.store_atomic_fact(atomic_fact),
            AndChainAtomicFact::AndFact(and_fact) => self.store_and_fact(and_fact),
            AndChainAtomicFact::ChainFact(chain_fact) => self.store_chain_fact(chain_fact),
        }
    }

    pub fn store_or_and_chain_atomic_fact(
        &mut self,
        fact: OrAndChainAtomicFact,
    ) -> Result<(), RuntimeError> {
        match fact {
            OrAndChainAtomicFact::AtomicFact(atomic_fact) => self.store_atomic_fact(atomic_fact),
            OrAndChainAtomicFact::AndFact(and_fact) => self.store_and_fact(and_fact),
            OrAndChainAtomicFact::ChainFact(chain_fact) => self.store_chain_fact(chain_fact),
            OrAndChainAtomicFact::OrFact(or_fact) => self.store_or_fact(or_fact),
        }
    }

    fn store_chain_fact(&mut self, chain_fact: ChainFact) -> Result<(), RuntimeError> {
        let atomic_facts = chain_fact
            .facts_with_order_transitive_closure()
            .map_err(RuntimeError::wrap_new_fact_as_store_conflict)?;
        for atomic_fact in atomic_facts {
            self.store_atomic_fact(atomic_fact)?;
        }
        Ok(())
    }

    pub fn store_chain_fact_by_ref(&mut self, chain_fact: &ChainFact) -> Result<(), RuntimeError> {
        self.store_chain_fact(chain_fact.clone())
    }

    pub fn store_equality(&mut self, equality: &EqualFact) -> Result<(), RuntimeError> {
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

        if let Some(derived) =
            super::equality_linear_derive::maybe_derived_linear_equal_fact(equality)
        {
            if derived.left.to_string() != derived.right.to_string() {
                self.store_equality(&derived)?;
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
    pub fn store_transitive_prop_name(&mut self, prop_name: String) {
        self.known_transitive_props.insert(prop_name, ());
    }

    pub fn store_reflexive_prop_name(&mut self, prop_name: String) {
        self.known_reflexive_props.insert(prop_name, ());
    }

    pub fn store_antisymmetric_prop_name(&mut self, prop_name: String) {
        self.known_antisymmetric_props.insert(prop_name, ());
    }

    pub fn store_symmetric_prop_permutation(
        &mut self,
        prop_name: String,
        gather: Vec<usize>,
        line_file: LineFile,
    ) -> Result<(), RuntimeError> {
        let n = gather.len();
        if n < 2 {
            return Err(
                StoreFactRuntimeError(RuntimeErrorStruct::new_with_msg_and_line_file(
                    "store_symmetric_prop_permutation: arity must be at least 2".to_string(),
                    line_file,
                ))
                .into(),
            );
        }
        if !symmetric_gather_is_valid_permutation(&gather, n) {
            return Err(
                StoreFactRuntimeError(RuntimeErrorStruct::new_with_msg_and_line_file(
                    "store_symmetric_prop_permutation: gather is not a valid permutation"
                        .to_string(),
                    line_file,
                ))
                .into(),
            );
        }
        if symmetric_gather_is_identity(&gather) {
            return Err(
                StoreFactRuntimeError(RuntimeErrorStruct::new_with_msg_and_line_file(
                    "store_symmetric_prop_permutation: identity permutation is not allowed"
                        .to_string(),
                    line_file,
                ))
                .into(),
            );
        }
        if let Some(existing) = self.known_symmetric_props.get(&prop_name) {
            if let Some(first) = existing.first() {
                if first.len() != n {
                    return Err(StoreFactRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(
                            format!(
                            "store_symmetric_prop_permutation: `{}` already has arity {}, got {}",
                            prop_name,
                            first.len(),
                            n
                        ),
                            line_file,
                        ),
                    )
                    .into());
                }
            }
        }
        let entry = self
            .known_symmetric_props
            .entry(prop_name)
            .or_insert_with(Vec::new);
        if entry.iter().any(|g| g == &gather) {
            return Ok(());
        }
        entry.push(gather);
        Ok(())
    }
}

impl Environment {
    pub fn store_fact_to_cache_known_fact(
        &mut self,
        fact_key: FactString,
        fact_line_file: LineFile,
    ) -> Result<(), RuntimeError> {
        self.store_fact_to_cache_known_fact_with_trust(
            fact_key,
            fact_line_file,
            ProofTrustSummary::new(),
        )
    }

    pub fn store_fact_to_cache_known_fact_with_trust(
        &mut self,
        fact_key: FactString,
        fact_line_file: LineFile,
        trust_summary: ProofTrustSummary,
    ) -> Result<(), RuntimeError> {
        self.cache_known_fact
            .insert(fact_key.clone(), fact_line_file);
        if !trust_summary.is_empty() {
            self.cache_known_fact_trust.insert(fact_key, trust_summary);
        }
        Ok(())
    }
}

pub fn atomic_fact_in_forall_arg_shape_key(
    atomic_fact: &AtomicFact,
) -> AtomicFactInForallArgShapeKey {
    atomic_fact
        .args_ref()
        .into_iter()
        .map(|arg| arg.equality_in_forall_key_part())
        .collect()
}

pub struct KnownForallFactParamsAndDom {
    pub params_def: ParamDefWithType,
    pub dom: Vec<Fact>,
    pub line_file: LineFile,
}

impl KnownForallFactParamsAndDom {
    pub fn new(params: ParamDefWithType, dom: Vec<Fact>, line_file: LineFile) -> Self {
        KnownForallFactParamsAndDom {
            params_def: params,
            dom,
            line_file,
        }
    }
}

pub type SymmetricPropValue = Vec<Vec<usize>>;

fn symmetric_gather_is_identity(gather: &[usize]) -> bool {
    gather.iter().enumerate().all(|(i, &g)| g == i)
}

fn symmetric_gather_is_valid_permutation(gather: &[usize], n: usize) -> bool {
    if gather.len() != n {
        return false;
    }
    let mut seen = vec![false; n];
    for &i in gather {
        if i >= n {
            return false;
        }
        if seen[i] {
            return false;
        }
        seen[i] = true;
    }
    true
}

fn atomic_fact_has_top_level_fn_arg_head_with_forall_free_param(atomic_fact: &AtomicFact) -> bool {
    atomic_fact
        .args_ref()
        .into_iter()
        .any(obj_is_fn_obj_with_forall_free_param_in_head)
}

fn obj_is_fn_obj_with_forall_free_param_in_head(obj: &Obj) -> bool {
    match obj {
        Obj::FnObj(fn_obj) => fn_obj.head.contains_forall_free_param_obj(),
        _ => false,
    }
}
