use super::helper::chain_line_file;
use super::store_fact_and_infer_result::{
    StoreAndComponentResult, StoreAndFactResult, StoreAtomicFactResult, StoreChainAdjacentResult,
    StoreChainFactStorePart, StoreExistShapedFactResult, StoreFactResult, StoreForallFactResult,
    StoreForallFactWithIffResult, StoreNotForallFactStorePart, StoreOrFactResult,
};
use crate::new_pipeline::ast::fact::atomic_fact_has_positive_polarity;
use crate::new_pipeline::ast::fact::{
    exist_shaped_fact_from_fact, exist_shaped_fact_id, exist_shaped_fact_to_fact, AndFact,
    AtomicFact, ChainFact, ExistShapedFact, Fact, ForallFact, ForallFactWithIff, NotForallFact,
    OrFact,
};
use crate::new_pipeline::exec_env::maybe_index_known_closed_numeric_equal;
use crate::new_pipeline::runtime::{FactId, Runtime, RuntimeResult};

impl Runtime {
    // Index a fact by shape into known-* / facts_by_id. No mathematical consequences.
    // Example: store `1 < 2 and 2 < 3` records the whole and indexes each atomic conjunct.
    pub fn store_fact(&mut self, fact: &Fact) -> RuntimeResult<StoreFactResult> {
        match fact {
            Fact::AtomicFact(atomic) => {
                self.store_atomic_fact(atomic)?;
                Ok(StoreFactResult::AtomicFact(StoreAtomicFactResult {
                    fact_id: atomic.fact_id(),
                    fact: atomic.clone(),
                }))
            }
            Fact::AndFact(and_fact) => {
                let stored = self.store_and_fact(and_fact)?;
                Ok(StoreFactResult::AndFact(stored))
            }
            Fact::ChainFact(chain_fact) => {
                let stored = self.store_chain_fact(chain_fact)?;
                Ok(StoreFactResult::ChainFact(stored))
            }
            Fact::OrFact(or_fact) => {
                let stored = self.store_or_fact(or_fact)?;
                Ok(StoreFactResult::OrFact(stored))
            }
            Fact::ExistFact(_) | Fact::ExistUniqueFact(_) | Fact::NotExistFact(_) => {
                let family = exist_shaped_fact_from_fact(fact).expect("exist family from fact");
                let stored = self.store_exist_shaped_fact(&family)?;
                Ok(StoreFactResult::ExistShapedFact(stored))
            }
            Fact::NotForall(not_forall) => {
                let stored = self.store_not_forall_fact(not_forall)?;
                Ok(StoreFactResult::NotForallFact(stored))
            }
            Fact::ForallFact(forall) => {
                let stored = self.store_forall_fact(forall)?;
                Ok(StoreFactResult::ForallFact(stored))
            }
            Fact::ForallFactWithIff(forall_iff) => {
                let stored = self.store_forall_fact_with_iff(forall_iff)?;
                Ok(StoreFactResult::ForallFactWithIff(stored))
            }
        }
    }

    // Index one atomic into known-* only.
    // Example: store `a = b` updates equivalence classes; store `x $in S` indexes the in-fact.
    pub fn store_atomic_fact(&mut self, atomic_fact: &AtomicFact) -> RuntimeResult<Vec<FactId>> {
        match atomic_fact {
            AtomicFact::EqualFact(equal_fact) => {
                let fact_id = equal_fact.fact_id;
                let env = self.top_exec_env_mut();
                env.facts.known_equivalence_classes.store(equal_fact);
                maybe_index_known_closed_numeric_equal(
                    &mut env.facts.known_closed_numeric_equal,
                    equal_fact,
                );
                env.facts
                    .known_equal_to_obj_with_free_params
                    .maybe_index(equal_fact);
                env.facts.record_atomic_fact(fact_id, atomic_fact.clone());
                Ok(vec![fact_id])
            }
            _ => {
                let fact_id = atomic_fact.fact_id();
                let key = atomic_fact.prop_name();
                let positive_polarity = atomic_fact_has_positive_polarity(atomic_fact);
                let env = self.top_exec_env_mut();
                env.facts.known_atomic_except_equality_facts.store(
                    key,
                    positive_polarity,
                    atomic_fact.clone(),
                );
                env.facts.record_atomic_fact(fact_id, atomic_fact.clone());
                Ok(vec![fact_id])
            }
        }
    }

    fn index_forall_chain_components(&mut self, forall: &ForallFact) -> RuntimeResult<()> {
        let mut projections = Vec::new();
        for (then_index, then) in forall.then_facts.iter().enumerate() {
            if let crate::new_pipeline::ast::fact::ExistOrAndChainAtomicFact::ChainFact(chain) =
                then
            {
                projections.push((then_index, self.chain_adjacent_atomics(chain)?));
            }
        }
        let memory = &mut self.top_exec_env_mut().facts.known_forall_conclusions;
        for (then_index, adjacent) in projections {
            memory.index_chain_components(forall, then_index, &adjacent);
        }
        Ok(())
    }

    // Forall: record whole into facts_by_id / known_forall; index chain then-edges.
    // Example: `forall x, y, z R: x < y < z` → known_forall + adjacent cites for x<y, y<z.
    fn store_forall_fact(&mut self, forall: &ForallFact) -> RuntimeResult<StoreForallFactResult> {
        let fact_id = forall.fact_id;
        self.top_exec_env_mut()
            .facts
            .record_fact(fact_id, Fact::ForallFact(forall.clone()));
        self.index_forall_chain_components(forall)?;
        Ok(StoreForallFactResult {
            fact_id,
            fact: forall.clone(),
        })
    }

    // Forall-iff: split into two foralls, store each direction.
    // Example:
    //   forall x, y R:
    //       =>:
    //           x = y
    //       <=>:
    //           y = x
    // → store both directions as ordinary forall facts.
    fn store_forall_fact_with_iff(
        &mut self,
        forall_iff: &ForallFactWithIff,
    ) -> RuntimeResult<StoreForallFactWithIffResult> {
        let (forward, reverse) = self.forall_with_iff_to_two_directions_for_store(forall_iff);
        let forward = self.store_forall_fact(&forward)?;
        let reverse = self.store_forall_fact(&reverse)?;
        Ok(StoreForallFactWithIffResult {
            fact_id: forall_iff.fact_id,
            fact: forall_iff.clone(),
            forward,
            reverse,
        })
    }

    fn forall_with_iff_to_two_directions_for_store(
        &mut self,
        forall_iff: &ForallFactWithIff,
    ) -> (ForallFact, ForallFact) {
        let f = &forall_iff.forall_fact;
        let line_file = forall_iff.line_file.clone().or_else(|| f.line_file.clone());
        let mut dom_then = f.dom_facts.clone();
        dom_then.extend(f.then_facts.iter().cloned().map(Fact::from));
        let forward = ForallFact {
            fact_id: self.ids.allocate_fact_id(),
            typed_parameters: f.typed_parameters.clone(),
            dom_facts: dom_then,
            then_facts: forall_iff.iff_facts.clone(),
            line_file: line_file.clone(),
        };
        let mut dom_iff = f.dom_facts.clone();
        dom_iff.extend(forall_iff.iff_facts.iter().cloned().map(Fact::from));
        let reverse = ForallFact {
            fact_id: self.ids.allocate_fact_id(),
            typed_parameters: f.typed_parameters.clone(),
            dom_facts: dom_iff,
            then_facts: f.then_facts.clone(),
            line_file,
        };
        (forward, reverse)
    }

    // And: record whole, then store each atomic component into known-* indexes.
    // Example: `1 < 2 and 2 < 3` → whole + known(1<2) + known(2<3).
    fn store_and_fact(&mut self, and_fact: &AndFact) -> RuntimeResult<StoreAndFactResult> {
        let whole_fact_id = and_fact.fact_id;
        self.top_exec_env_mut()
            .facts
            .record_fact(whole_fact_id, Fact::AndFact(and_fact.clone()));

        let mut components = Vec::with_capacity(and_fact.facts.len());
        for (component_index, atomic) in and_fact.facts.iter().enumerate() {
            self.store_atomic_fact(atomic)?;
            components.push(StoreAndComponentResult {
                component_index,
                fact_id: atomic.fact_id(),
                fact: atomic.clone(),
            });
        }
        Ok(StoreAndFactResult {
            whole_fact_id,
            fact: and_fact.clone(),
            components,
        })
    }

    // Or: record whole into facts_by_id and known_or. Do not split branches.
    // Example: `1 = 1 or 1 = 2` → known_or only.
    fn store_or_fact(&mut self, or_fact: &OrFact) -> RuntimeResult<StoreOrFactResult> {
        let whole_fact_id = or_fact.fact_id;
        let env = self.top_exec_env_mut();
        env.facts.known_or.store(or_fact);
        env.facts
            .record_fact(whole_fact_id, Fact::OrFact(or_fact.clone()));
        Ok(StoreOrFactResult {
            whole_fact_id,
            fact: or_fact.clone(),
        })
    }

    // Exist: record whole into facts_by_id and known_exist. Do not split body.
    // Example: `exist x N st {x = 1}` → known_exist only.
    pub(crate) fn store_exist_shaped_fact(
        &mut self,
        exist_fact: &ExistShapedFact,
    ) -> RuntimeResult<StoreExistShapedFactResult> {
        let whole_fact_id = exist_shaped_fact_id(exist_fact);
        let env = self.top_exec_env_mut();
        env.facts.known_exist.store(exist_fact);
        env.facts
            .record_fact(whole_fact_id, exist_shaped_fact_to_fact(exist_fact));
        Ok(StoreExistShapedFactResult {
            whole_fact_id,
            fact: exist_fact.clone(),
        })
    }

    // NotForall: record the sugar fact only. Counterexample exist is infer.
    // Example: `not forall x R: x > 0` → facts_by_id(not forall).
    fn store_not_forall_fact(
        &mut self,
        not_forall: &NotForallFact,
    ) -> RuntimeResult<StoreNotForallFactStorePart> {
        let whole_fact_id = not_forall.fact_id;
        self.top_exec_env_mut()
            .facts
            .record_fact(whole_fact_id, Fact::NotForall(not_forall.clone()));
        Ok(StoreNotForallFactStorePart {
            whole_fact_id,
            fact: not_forall.clone(),
        })
    }

    // Chain: record whole and store adjacent edges. Transitive closures are infer.
    // Example: `a < b < c` → whole + adjacent a<b, b<c.
    fn store_chain_fact(
        &mut self,
        chain_fact: &ChainFact,
    ) -> RuntimeResult<StoreChainFactStorePart> {
        let whole_fact_id = chain_fact.fact_id;
        self.top_exec_env_mut()
            .facts
            .record_fact(whole_fact_id, Fact::ChainFact(chain_fact.clone()));

        let adjacent_atomics = self.chain_adjacent_atomics(chain_fact)?;
        let mut adjacent = Vec::with_capacity(adjacent_atomics.len());
        for (edge_index, atomic) in adjacent_atomics.into_iter().enumerate() {
            self.store_atomic_fact(&atomic)?;
            adjacent.push(StoreChainAdjacentResult {
                edge_index,
                fact_id: atomic.fact_id(),
                fact: atomic,
            });
        }

        Ok(StoreChainFactStorePart {
            whole_fact_id,
            fact: chain_fact.clone(),
            adjacent,
        })
    }

    pub(crate) fn chain_adjacent_atomics(
        &mut self,
        chain_fact: &ChainFact,
    ) -> RuntimeResult<Vec<AtomicFact>> {
        if chain_fact.objs.len() != chain_fact.prop_names.len() + 1 {
            return Err(crate::new_pipeline::runtime::RuntimeError::InternalBug(
                format!(
                    "chain fact object count {} != prop count {} + 1",
                    chain_fact.objs.len(),
                    chain_fact.prop_names.len()
                ),
            ));
        }
        let line_file = chain_line_file(chain_fact);
        let mut facts = Vec::with_capacity(chain_fact.prop_names.len());
        for i in 0..chain_fact.prop_names.len() {
            let atomic = self.atomic_from_prop(
                chain_fact.prop_names[i].clone(),
                vec![chain_fact.objs[i].clone(), chain_fact.objs[i + 1].clone()],
                true,
                line_file.clone(),
            )?;
            facts.push(atomic);
        }
        Ok(facts)
    }
}
