//! Central fact-storage dispatch and its fact-shape branches.

use crate::prelude::*;
use std::collections::HashMap;
use std::rc::Rc;

impl ExecEnv {
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
                self.facts
                    .special_set_relations
                    .owner_sets
                    .entry(element_key.clone())
                    .or_default()
                    .entry(set_key)
                    .or_insert_with(|| in_fact.clone());

                if let Obj::PowerSet(power_set) = &in_fact.set {
                    self.facts
                        .special_set_relations
                        .direct_supersets
                        .entry(element_key)
                        .or_default()
                        .entry(obj_equality_key(power_set.set.as_ref()))
                        .or_insert_with(|| atomic_fact.clone());
                }
            }
            AtomicFact::SubsetFact(subset_fact) => {
                self.facts
                    .special_set_relations
                    .direct_supersets
                    .entry(obj_equality_key(&subset_fact.left))
                    .or_default()
                    .entry(obj_equality_key(&subset_fact.right))
                    .or_insert_with(|| atomic_fact.clone());
            }
            AtomicFact::SupersetFact(superset_fact) => {
                self.facts
                    .special_set_relations
                    .direct_supersets
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
                let positive_polarity = atomic_fact.has_positive_polarity();
                let (arg_len, arg_key1, arg_key2) = {
                    let args = atomic_fact.args_ref();
                    let arg_key1 = args.first().map(|arg| arg.to_string());
                    let arg_key2 = args.get(1).map(|arg| arg.to_string());
                    (args.len(), arg_key1, arg_key2)
                };
                if arg_len == 1 {
                    let arg_key: ObjString = arg_key1.expect("one argument key should exist");
                    if let Some(map) = self
                        .facts
                        .known_atomic_except_equality_facts
                        .by_one_arg
                        .get_mut(&(key.clone(), positive_polarity))
                    {
                        map.insert(arg_key, atomic_fact);
                    } else {
                        self.facts.known_atomic_except_equality_facts.by_one_arg.insert(
                            (key, positive_polarity),
                            HashMap::from([(arg_key, atomic_fact)]),
                        );
                    }
                } else if arg_len == 2 {
                    let arg_key1: ObjString = arg_key1.expect("first argument key should exist");
                    let arg_key2: ObjString = arg_key2.expect("second argument key should exist");
                    if let Some(map) = self
                        .facts
                        .known_atomic_except_equality_facts
                        .by_two_args
                        .get_mut(&(key.clone(), positive_polarity))
                    {
                        map.insert((arg_key1, arg_key2), atomic_fact);
                    } else {
                        self.facts.known_atomic_except_equality_facts.by_two_args.insert(
                            (key, positive_polarity),
                            HashMap::from([((arg_key1, arg_key2), atomic_fact)]),
                        );
                    }
                } else {
                    if let Some(vec_ref) = self
                        .facts
                        .known_atomic_except_equality_facts
                        .by_other_arg_count
                        .get_mut(&(key.clone(), positive_polarity))
                    {
                        vec_ref.push(atomic_fact);
                    } else {
                        self.facts
                            .known_atomic_except_equality_facts
                            .by_other_arg_count
                            .insert((key, positive_polarity), vec![atomic_fact]);
                    }
                }
                Ok(())
            }
        }
    }

    fn store_exist_fact(&mut self, exist_fact: ExistFact) -> Result<(), RuntimeError> {
        let key: ExistFactKey = exist_fact.key();
        if let Some(vec_ref) = self.facts.known_exist.by_key.get_mut(&key) {
            vec_ref.push(exist_fact.clone());
        } else {
            self.facts
                .known_exist
                .by_key
                .insert(key.clone(), vec![exist_fact.clone()]);
        }
        let alpha_key = exist_fact.alpha_normalized_key();
        if alpha_key != key {
            if let Some(vec_ref) = self.facts.known_exist.by_key.get_mut(&alpha_key) {
                vec_ref.push(exist_fact);
            } else {
                self.facts
                    .known_exist
                    .by_key
                    .insert(alpha_key, vec![exist_fact]);
            }
        }
        Ok(())
    }

    fn store_or_fact(&mut self, or_fact: OrFact) -> Result<(), RuntimeError> {
        let key: OrFactKey = or_fact.key();
        if let Some(vec_ref) = self.facts.known_or.by_key.get_mut(&key) {
            vec_ref.push(or_fact);
        } else {
            self.facts.known_or.by_key.insert(key, vec![or_fact]);
        }
        Ok(())
    }

    fn store_atomic_fact_in_forall_fact(
        &mut self,
        atomic_fact: AtomicFact,
        stored_forall_conclusion_reference: Rc<StoredForallConclusionReference>,
    ) -> Result<(), RuntimeError> {
        let key: AtomicFactKey = atomic_fact.key();
        let positive_polarity = atomic_fact.has_positive_polarity();

        if atomic_fact_has_top_level_fn_arg_head_with_forall_free_param(&atomic_fact) {
            let lookup_key = (key, positive_polarity);
            if let Some(vec_ref) = self
                .facts
                .forall_conclusions
                .atomic_with_parameterized_head
                .get_mut(&lookup_key)
            {
                vec_ref.push((atomic_fact, stored_forall_conclusion_reference));
            } else {
                self.facts
                    .forall_conclusions
                    .atomic_with_parameterized_head
                    .insert(
                        lookup_key,
                        vec![(atomic_fact, stored_forall_conclusion_reference)],
                    );
            }
            return Ok(());
        }

        let lookup_key = (key, positive_polarity);
        let arg_shape_key = forall_argument_shape(&atomic_fact);
        let arg_shape_map = self
            .facts
            .forall_conclusions
            .atomic_by_argument_shape
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
        if let Some(vec_ref) = self.facts.forall_conclusions.disjunction.get_mut(&key) {
            vec_ref.push((or_fact.clone(), stored_forall_conclusion_reference));
        } else {
            self.facts.forall_conclusions.disjunction.insert(
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
        if let Some(vec_ref) = self.facts.forall_conclusions.conjunction.get_mut(&key) {
            vec_ref.push((and_fact.clone(), stored_forall_conclusion_reference));
        } else {
            self.facts.forall_conclusions.conjunction.insert(
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
            .facts(&Runtime::default())
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
        exist_fact: &ExistFact,
        stored_forall_conclusion_reference: Rc<StoredForallConclusionReference>,
    ) -> Result<(), RuntimeError> {
        let pair = || {
            (
                exist_fact.clone(),
                stored_forall_conclusion_reference.clone(),
            )
        };
        let key: ExistFactKey = exist_fact.key();
        if let Some(vec_ref) = self.facts.forall_conclusions.existential.get_mut(&key) {
            vec_ref.push(pair());
        } else {
            self.facts
                .forall_conclusions
                .existential
                .insert(key, vec![pair()]);
        }
        let alpha_key = exist_fact.alpha_normalized_key();
        if alpha_key != exist_fact.key() {
            if let Some(vec_ref) = self
                .facts
                .forall_conclusions
                .existential
                .get_mut(&alpha_key)
            {
                vec_ref.push(pair());
            } else {
                self.facts
                    .forall_conclusions
                    .existential
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
            forall_fact_with_iff.to_two_forall_facts(&Runtime::default())?;
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

    pub fn store_exist_fact_by_ref(&mut self, exist_fact: &ExistFact) -> Result<(), RuntimeError> {
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
            .facts_with_order_transitive_closure_with_runtime(&Runtime::default())
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
        self.facts.known_equality.store(equality);

        if let Some(derived) = super::equality_linear_derive::maybe_derived_linear_equal_fact(
            &Runtime::default(),
            equality,
        ) {
            if obj_equality_key(&derived.left) != obj_equality_key(&derived.right) {
                self.store_equality(&derived)?;
            }
        }
        Ok(())
    }
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
