use super::known_fn::KnownFnInfo;
use crate::prelude::*;
use std::collections::HashMap;
use std::fmt;
use std::ops::{Deref, DerefMut};
use std::rc::Rc;

pub type AtomicFactInForallArgShapeKey = Vec<(ObjKind, ObjOperatorString)>;
pub type AtomicFactInForallArgShapeIndex = HashMap<
    (AtomicFactKey, bool),
    HashMap<AtomicFactInForallArgShapeKey, Vec<(AtomicFact, Rc<StoredForallConclusionReference>)>>,
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
    /// Persistent repositories that describe the checked mathematical world.
    /// Statement-local proof search state belongs to `Runtime`, not here.
    pub repositories: EnvironmentPersistentRepositories,
}

impl Deref for Environment {
    type Target = EnvironmentPersistentRepositories;

    fn deref(&self) -> &Self::Target {
        &self.repositories
    }
}

impl DerefMut for Environment {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.repositories
    }
}

/// Named aggregate for all persistent Environment repositories.
///
/// The fields retain their domain names because verifier code addresses the
/// corresponding indexes directly; grouping them here keeps `Environment`
/// itself a clear owner instead of a mixture of persistent data and runtime
/// scratch state.
#[derive(Clone)]
pub struct EnvironmentPersistentRepositories {
    pub symbols: SymbolTable,
    pub defined_identifiers: HashMap<IdentifierName, ParamObjType>,
    pub defined_def_props: HashMap<PropName, DefPropStmt>,
    pub defined_abstract_props: HashMap<AbstractPropName, DefAbstractPropStmt>,
    pub defined_algorithms: HashMap<AlgoName, DefAlgoStmt>,
    pub defined_structs: HashMap<StructName, DefStructStmt>,
    pub defined_templates: HashMap<TemplateName, DefTemplateStmt>,
    pub defined_settings: HashMap<String, DefSettingStmt>,
    pub defined_thm_stmts: HashMap<ThmName, DefThmStmt>,
    pub defined_axiom_stmts: HashMap<ThmName, AxiomStmt>,
    pub defined_strategy_stmts: HashMap<StrategyName, DefStrategyStmt>,

    pub known_equality: KnownEquality,

    pub known_atomic_facts_with_0_or_more_than_2_args:
        HashMap<(AtomicFactKey, bool), Vec<AtomicFact>>,
    pub known_atomic_facts_with_1_arg:
        HashMap<(AtomicFactKey, bool), HashMap<ObjString, AtomicFact>>,
    pub known_atomic_facts_with_2_args:
        HashMap<(AtomicFactKey, bool), HashMap<(ObjString, ObjString), AtomicFact>>,
    pub known_owner_sets: HashMap<ObjString, HashMap<ObjString, InFact>>,
    pub known_direct_supersets: HashMap<ObjString, HashMap<ObjString, AtomicFact>>,

    pub known_exist_facts: HashMap<ExistFactKey, Vec<ExistFactEnum>>,
    pub known_or_facts: HashMap<OrFactKey, Vec<OrFact>>,

    pub known_atomic_facts_in_forall_facts:
        HashMap<(AtomicFactKey, bool), Vec<(AtomicFact, Rc<StoredForallConclusionReference>)>>,
    pub known_atomic_facts_in_forall_facts_by_arg_shape: AtomicFactInForallArgShapeIndex,
    pub known_exist_facts_in_forall_facts:
        HashMap<ExistFactKey, Vec<(ExistFactEnum, Rc<StoredForallConclusionReference>)>>,
    pub known_and_facts_in_forall_facts:
        HashMap<AndFactKey, Vec<(AndFact, Rc<StoredForallConclusionReference>)>>,
    pub known_or_facts_in_forall_facts:
        HashMap<OrFactKey, Vec<(OrFact, Rc<StoredForallConclusionReference>)>>,

    pub known_objs_equal_to_tuple: HashMap<ObjString, (Option<Tuple>, Option<Cart>, LineFile)>,
    pub known_objs_equal_to_cart: HashMap<ObjString, (Cart, LineFile)>,
    pub known_objs_equal_to_finite_seq_list:
        HashMap<ObjString, (FiniteSeqListObj, Option<FiniteSeqSet>, LineFile)>,
    pub known_objs_equal_to_matrix_list:
        HashMap<ObjString, (MatrixListObj, Option<MatrixSet>, LineFile)>,
    pub known_objs_in_matrix_sets: HashMap<ObjString, (MatrixSet, LineFile)>,
    pub known_obj_values: HashMap<ObjString, KnownObjValue>,
    pub known_objs_equal_to_set_builder: HashMap<ObjString, (SetBuilder, LineFile)>,

    pub known_objs_in_fn_sets: HashMap<ObjString, KnownFnInfo>,

    pub known_transitive_props: HashMap<String, ()>,
    pub known_symmetric_props: HashMap<String, SymmetricPropValue>,
    pub known_reflexive_props: HashMap<String, ()>,
    pub known_antisymmetric_props: HashMap<String, ()>,

    pub cache_well_defined_obj: HashMap<WellDefinedCacheKey, CachedWellDefinedObj>,
    pub stored_facts: EnvironmentStoredFactRepository,
    pub cache_infer_rule_firing: HashMap<String, ()>,
    pub used_strategy_stmts: HashMap<(PropName, bool), StrategyName>,
    pub stopped_strategy_stmts: HashMap<(PropName, bool), StrategyName>,
}

#[derive(Clone)]
pub enum KnownObjValue {
    SimplifiedNumber(Number), // when a = 1.0, store a = 1
    SimplifiedFraction(Div),  // when a = 1/3, store a = 1/3
}

impl fmt::Display for Environment {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "Environment {{\n")?;
        write!(f, "    objs: {:?}\n", self.defined_identifiers.len())?;
        write!(f, "    def_props: {:?}\n", self.defined_def_props.len())?;
        write!(f, "    algorithms: {:?}\n", self.defined_algorithms.len())?;
        write!(f, "    structs: {:?}\n", self.defined_structs.len())?;
        write!(f, "    templates: {:?}\n", self.defined_templates.len())?;
        write!(f, "    settings: {:?}\n", self.defined_settings.len())?;
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
            "    stored_fact_lookup_keys: {:?}\n",
            self.stored_facts.lookup_key_count()
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
        match &atomic_fact {
            AtomicFact::InFact(in_fact) => {
                let element_key = obj_equality_key(&in_fact.element);
                let set_key = obj_equality_key(&in_fact.set);
                self.known_owner_sets
                    .entry(element_key.clone())
                    .or_default()
                    .entry(set_key)
                    .or_insert_with(|| in_fact.clone());

                if let Obj::PowerSet(power_set) = &in_fact.set {
                    self.known_direct_supersets
                        .entry(element_key)
                        .or_default()
                        .entry(obj_equality_key(power_set.set.as_ref()))
                        .or_insert_with(|| atomic_fact.clone());
                }
            }
            AtomicFact::SubsetFact(subset_fact) => {
                self.known_direct_supersets
                    .entry(obj_equality_key(&subset_fact.left))
                    .or_default()
                    .entry(obj_equality_key(&subset_fact.right))
                    .or_insert_with(|| atomic_fact.clone());
            }
            AtomicFact::SupersetFact(superset_fact) => {
                self.known_direct_supersets
                    .entry(obj_equality_key(&superset_fact.right))
                    .or_default()
                    .entry(obj_equality_key(&superset_fact.left))
                    .or_insert_with(|| atomic_fact.clone());
            }
            _ => {}
        }

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
            vec_ref.push(exist_fact.clone());
        } else {
            self.known_exist_facts
                .insert(key.clone(), vec![exist_fact.clone()]);
        }
        let alpha_key = exist_fact.alpha_normalized_key();
        if alpha_key != key {
            if let Some(vec_ref) = self.known_exist_facts.get_mut(&alpha_key) {
                vec_ref.push(exist_fact);
            } else {
                self.known_exist_facts.insert(alpha_key, vec![exist_fact]);
            }
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
        stored_forall_conclusion_reference: Rc<StoredForallConclusionReference>,
    ) -> Result<(), RuntimeError> {
        let key: AtomicFactKey = atomic_fact.key();
        let is_true = atomic_fact.is_true();

        if atomic_fact_has_top_level_fn_arg_head_with_forall_free_param(&atomic_fact) {
            let lookup_key = (key, is_true);
            if let Some(vec_ref) = self.known_atomic_facts_in_forall_facts.get_mut(&lookup_key) {
                vec_ref.push((atomic_fact, stored_forall_conclusion_reference));
            } else {
                self.known_atomic_facts_in_forall_facts.insert(
                    lookup_key,
                    vec![(atomic_fact, stored_forall_conclusion_reference)],
                );
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
            .push((atomic_fact, stored_forall_conclusion_reference));
        Ok(())
    }

    fn store_or_fact_in_forall_fact(
        &mut self,
        or_fact: &OrFact,
        stored_forall_conclusion_reference: Rc<StoredForallConclusionReference>,
    ) -> Result<(), RuntimeError> {
        let key: OrFactKey = or_fact.key();
        if let Some(vec_ref) = self.known_or_facts_in_forall_facts.get_mut(&key) {
            vec_ref.push((or_fact.clone(), stored_forall_conclusion_reference));
        } else {
            self.known_or_facts_in_forall_facts.insert(
                key,
                vec![(or_fact.clone(), stored_forall_conclusion_reference)],
            );
        }
        Ok(())
    }

    fn store_whole_and_fact_in_forall_fact(
        &mut self,
        and_fact: &AndFact,
        stored_forall_conclusion_reference: Rc<StoredForallConclusionReference>,
    ) -> Result<(), RuntimeError> {
        let key: AndFactKey = and_fact.key();
        if let Some(vec_ref) = self.known_and_facts_in_forall_facts.get_mut(&key) {
            vec_ref.push((and_fact.clone(), stored_forall_conclusion_reference));
        } else {
            self.known_and_facts_in_forall_facts.insert(
                key,
                vec![(and_fact.clone(), stored_forall_conclusion_reference)],
            );
        }
        Ok(())
    }

    fn store_a_fact_in_forall_fact(
        &mut self,
        fact: &ExistOrAndChainAtomicFact,
        stored_forall_conclusion_reference: Rc<StoredForallConclusionReference>,
    ) -> Result<(), RuntimeError> {
        match fact {
            ExistOrAndChainAtomicFact::AtomicFact(spec_fact) => self
                .store_atomic_fact_in_forall_fact(
                    spec_fact.clone(),
                    stored_forall_conclusion_reference,
                ),
            ExistOrAndChainAtomicFact::OrFact(or_fact) => {
                self.store_or_fact_in_forall_fact(&or_fact, stored_forall_conclusion_reference)
            }
            ExistOrAndChainAtomicFact::AndFact(and_fact) => {
                self.store_and_fact_in_forall_fact(&and_fact, stored_forall_conclusion_reference)
            }
            ExistOrAndChainAtomicFact::ChainFact(chain_fact) => self
                .store_chain_fact_in_forall_fact(&chain_fact, stored_forall_conclusion_reference),
            ExistOrAndChainAtomicFact::ExistFact(exist_fact) => self
                .store_exist_fact_in_forall_fact(&exist_fact, stored_forall_conclusion_reference),
        }
    }

    fn store_chain_fact_in_forall_fact(
        &mut self,
        chain_fact: &ChainFact,
        stored_forall_conclusion_reference: Rc<StoredForallConclusionReference>,
    ) -> Result<(), RuntimeError> {
        for (component_index, fact) in chain_fact
            .facts()
            .map_err(RuntimeError::wrap_new_fact_as_store_conflict)?
            .into_iter()
            .enumerate()
        {
            self.store_atomic_fact_in_forall_fact(
                fact,
                stored_forall_conclusion_reference.with_conclusion_location(
                    ForallConclusionLocation::chain_fact_component(
                        stored_forall_conclusion_reference
                            .conclusion_location
                            .then_fact_index(),
                        component_index,
                    ),
                ),
            )?;
        }
        Ok(())
    }

    fn store_exist_fact_in_forall_fact(
        &mut self,
        exist_fact: &ExistFactEnum,
        stored_forall_conclusion_reference: Rc<StoredForallConclusionReference>,
    ) -> Result<(), RuntimeError> {
        let pair = || {
            (
                exist_fact.clone(),
                stored_forall_conclusion_reference.clone(),
            )
        };
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
        stored_forall_conclusion_reference: Rc<StoredForallConclusionReference>,
    ) -> Result<(), RuntimeError> {
        self.store_whole_and_fact_in_forall_fact(
            and_fact,
            stored_forall_conclusion_reference.clone(),
        )?;
        for (component_index, fact) in and_fact.facts.iter().enumerate() {
            self.store_atomic_fact_in_forall_fact(
                fact.clone(),
                stored_forall_conclusion_reference.with_conclusion_location(
                    ForallConclusionLocation::and_fact_component(
                        stored_forall_conclusion_reference
                            .conclusion_location
                            .then_fact_index(),
                        component_index,
                    ),
                ),
            )?;
        }
        Ok(())
    }

    fn store_forall_fact(
        &mut self,
        forall_fact: Rc<ForallFact>,
        source_fact_id: FactId,
    ) -> Result<(), RuntimeError> {
        for (then_fact_index, fact) in forall_fact.then_facts.iter().enumerate() {
            let known_forall_conclusion = Rc::new(StoredForallConclusionReference::new(
                forall_fact.clone(),
                source_fact_id,
                ForallConclusionLocation::direct_then_fact(then_fact_index),
            ));
            self.store_a_fact_in_forall_fact(fact, known_forall_conclusion)?;
        }
        Ok(())
    }

    /// Index an intentional additional structural spelling of an already
    /// stored universal fact under the FactId that owns the proposition.
    ///
    /// This does not create a second stored fact, cache alias, or inference
    /// event. It only makes the exact conclusion structure available to the
    /// known-forall matcher. Callers must already have established that the
    /// supplied universal is proposition-equivalent to `source_fact_id`.
    pub fn index_additional_structural_spelling_of_existing_forall_fact(
        &mut self,
        forall_fact: ForallFact,
        source_fact_id: FactId,
    ) -> Result<(), RuntimeError> {
        self.store_forall_fact(Rc::new(forall_fact), source_fact_id)
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
        source_fact_id: FactId,
    ) -> Result<(), RuntimeError> {
        let (forall_then_implies_iff, forall_iff_implies_then) =
            forall_fact_with_iff.to_two_forall_facts()?;
        self.store_forall_fact(Rc::new(forall_then_implies_iff), source_fact_id)?;
        self.store_forall_fact(Rc::new(forall_iff_implies_then), source_fact_id)?;
        Ok(())
    }

    pub fn store_fact(&mut self, fact: Fact, fact_id: FactId) -> Result<(), RuntimeError> {
        let equivalent_proposition_lookup_key = nested_obj_binder_normalized_fact_key(&fact);
        self.store_fact_with_equivalent_proposition_key(
            fact,
            fact_id,
            equivalent_proposition_lookup_key,
        )
    }

    pub fn store_fact_with_equivalent_proposition_key(
        &mut self,
        fact: Fact,
        fact_id: FactId,
        equivalent_proposition_lookup_key: FactString,
    ) -> Result<(), RuntimeError> {
        self.record_stored_fact_with_equivalent_proposition_key(
            fact.clone(),
            fact_id,
            equivalent_proposition_lookup_key,
        )?;
        match fact {
            Fact::AtomicFact(atomic_fact) => self.store_atomic_fact(atomic_fact),
            Fact::ExistFact(exist_fact) => self.store_exist_fact(exist_fact),
            Fact::OrFact(or_fact) => self.store_or_fact(or_fact),
            Fact::AndFact(and_fact) => self.store_and_fact(and_fact),
            Fact::ChainFact(chain_fact) => self.store_chain_fact(chain_fact),
            Fact::ForallFact(forall_fact) => self.store_forall_fact(Rc::new(forall_fact), fact_id),
            Fact::ForallFactWithIff(forall_fact_with_iff) => {
                self.store_forall_fact_with_iff(forall_fact_with_iff, fact_id)
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

    pub fn store_quantifier_free_fact(
        &mut self,
        fact: QuantifierFreeFact,
    ) -> Result<(), RuntimeError> {
        match fact {
            QuantifierFreeFact::AtomicFact(atomic_fact) => self.store_atomic_fact(atomic_fact),
            QuantifierFreeFact::AndFact(and_fact) => self.store_and_fact(and_fact),
            QuantifierFreeFact::ChainFact(chain_fact) => self.store_chain_fact(chain_fact),
            QuantifierFreeFact::OrFact(or_fact) => self.store_or_fact(or_fact),
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
        self.known_equality.store(equality);

        if let Some(derived) =
            super::equality_linear_derive::maybe_derived_linear_equal_fact(equality)
        {
            if obj_equality_key(&derived.left) != obj_equality_key(&derived.right) {
                self.store_equality(&derived)?;
            }
        }
        Ok(())
    }
}

impl Environment {
    pub fn new_empty_env() -> Self {
        Environment {
            repositories: EnvironmentPersistentRepositories {
                symbols: SymbolTable::new(),
                defined_identifiers: HashMap::new(),
                defined_def_props: HashMap::new(),
                defined_abstract_props: HashMap::new(),
                defined_algorithms: HashMap::new(),
                defined_structs: HashMap::new(),
                defined_templates: HashMap::new(),
                defined_settings: HashMap::new(),
                defined_thm_stmts: HashMap::new(),
                defined_axiom_stmts: HashMap::new(),
                defined_strategy_stmts: HashMap::new(),
                known_equality: KnownEquality::new(),
                known_atomic_facts_with_0_or_more_than_2_args: HashMap::new(),
                known_atomic_facts_with_1_arg: HashMap::new(),
                known_atomic_facts_with_2_args: HashMap::new(),
                known_owner_sets: HashMap::new(),
                known_direct_supersets: HashMap::new(),
                known_exist_facts: HashMap::new(),
                known_or_facts: HashMap::new(),
                known_atomic_facts_in_forall_facts: HashMap::new(),
                known_atomic_facts_in_forall_facts_by_arg_shape: HashMap::new(),
                known_exist_facts_in_forall_facts: HashMap::new(),
                known_and_facts_in_forall_facts: HashMap::new(),
                known_or_facts_in_forall_facts: HashMap::new(),
                known_objs_equal_to_tuple: HashMap::new(),
                known_objs_equal_to_cart: HashMap::new(),
                known_objs_equal_to_finite_seq_list: HashMap::new(),
                known_objs_equal_to_matrix_list: HashMap::new(),
                known_objs_in_matrix_sets: HashMap::new(),
                known_obj_values: HashMap::new(),
                known_objs_equal_to_set_builder: HashMap::new(),
                known_objs_in_fn_sets: HashMap::new(),
                known_transitive_props: HashMap::new(),
                known_symmetric_props: HashMap::new(),
                known_reflexive_props: HashMap::new(),
                known_antisymmetric_props: HashMap::new(),
                cache_well_defined_obj: HashMap::new(),
                stored_facts: EnvironmentStoredFactRepository::default(),
                cache_infer_rule_firing: HashMap::new(),
                used_strategy_stmts: HashMap::new(),
                stopped_strategy_stmts: HashMap::new(),
            },
        }
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
        fact_id: FactId,
    ) -> Result<(), RuntimeError> {
        self.stored_facts
            .record_lookup_key(fact_key, fact_line_file, fact_id)
    }

    pub fn store_fact_to_cache_known_fact_with_equivalent_proposition_key(
        &mut self,
        fact_key: FactString,
        fact_line_file: LineFile,
        fact_id: FactId,
        equivalent_proposition_lookup_key: FactString,
    ) -> Result<(), RuntimeError> {
        self.stored_facts
            .record_lookup_key_with_equivalent_proposition_key(
                fact_key,
                fact_line_file,
                fact_id,
                equivalent_proposition_lookup_key,
            )
    }

    pub fn record_stored_fact(&mut self, fact: Fact, fact_id: FactId) -> Result<(), RuntimeError> {
        self.stored_facts.record_fact(fact, fact_id)
    }

    pub fn record_stored_fact_with_equivalent_proposition_key(
        &mut self,
        fact: Fact,
        fact_id: FactId,
        equivalent_proposition_lookup_key: FactString,
    ) -> Result<(), RuntimeError> {
        self.stored_facts
            .record_fact_with_equivalent_proposition_key(
                fact,
                fact_id,
                equivalent_proposition_lookup_key,
            )
    }

    pub fn store_infer_rule_firing(&mut self, firing_key: String) {
        self.cache_infer_rule_firing.insert(firing_key, ());
    }
}

/// The deliberately small payload kept by the fact cache.
///
/// Proof trees, origins, scopes, and Lean names belong to statement Results
/// and compiler state. The environment only needs a stable identity and the
/// source location already used by diagnostics.
#[derive(Clone, Debug)]
pub struct CachedKnownFact {
    pub fact_id: FactId,
    pub line_file: LineFile,
    pub equivalent_proposition_lookup_key: FactString,
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

/// One conclusion indexed from one exact stored universal fact.
///
/// The complete source proposition and `FactId` remain together with the
/// structural conclusion location, so consumers never rebuild a smaller
/// universal from the matched conclusion.
pub struct StoredForallConclusionReference {
    pub params_def: ParamDefWithType,
    pub dom: Vec<Fact>,
    pub line_file: LineFile,
    /// Exact stored universal that produced every indexed conclusion sharing
    /// this record. A consumer may select one conclusion for matching, but its
    /// proof citation must retain this complete source proposition and FactId.
    pub source_forall: Rc<ForallFact>,
    pub source_fact_id: FactId,
    pub conclusion_location: ForallConclusionLocation,
}

impl StoredForallConclusionReference {
    pub fn new(
        source_forall: Rc<ForallFact>,
        source_fact_id: FactId,
        conclusion_location: ForallConclusionLocation,
    ) -> Self {
        StoredForallConclusionReference {
            params_def: source_forall.params_def_with_type.clone(),
            dom: source_forall.dom_facts.clone(),
            line_file: source_forall.line_file.clone(),
            source_forall,
            source_fact_id,
            conclusion_location,
        }
    }

    pub fn source_fact(&self) -> Fact {
        self.source_forall.as_ref().clone().into()
    }

    pub fn with_conclusion_location(
        &self,
        conclusion_location: ForallConclusionLocation,
    ) -> Rc<Self> {
        Rc::new(Self::new(
            self.source_forall.clone(),
            self.source_fact_id,
            conclusion_location,
        ))
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
