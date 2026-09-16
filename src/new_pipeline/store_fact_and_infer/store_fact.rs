use super::store_fact_and_infer_result::{
    ChainTransitiveCite, StoreAndComponentResult, StoreAndFactResult, StoreAtomicFactResult,
    StoreChainAdjacentResult, StoreChainFactResult, StoreChainTransitiveClosureResult,
    StoreFactAndInferResult, StoreOrFactResult,
};
use crate::new_pipeline::ast::fact::{AndFact, AtomicFact, ChainFact, Fact, OrFact};
use crate::new_pipeline::ast::line_file::LineFile;
use crate::new_pipeline::ast::names::AtomicName;
use crate::new_pipeline::exec_env::exec_env::PropRewriteProperty;
use crate::new_pipeline::exec_env::helper::atomic_fact_has_positive_polarity;
use crate::new_pipeline::parse::keywords::{
    EQUAL, GREATER, GREATER_EQUAL, LESS, LESS_EQUAL,
};
use crate::new_pipeline::runtime::{FactId, RealOrVirtualPath, Runtime, RuntimeResult};

impl Runtime {
    pub fn store_fact_and_infer(&mut self, fact: &Fact) -> RuntimeResult<StoreFactAndInferResult> {
        match fact {
            Fact::AtomicFact(atomic) => {
                self.store_atomic_fact(atomic)?;
                Ok(StoreFactAndInferResult::AtomicFact(StoreAtomicFactResult {
                    fact_id: atomic.fact_id(),
                    fact: atomic.clone(),
                }))
            }
            Fact::AndFact(and_fact) => {
                let stored = self.store_and_fact(and_fact)?;
                Ok(StoreFactAndInferResult::AndFact(stored))
            }
            Fact::ChainFact(chain_fact) => {
                let stored = self.store_chain_fact(chain_fact)?;
                Ok(StoreFactAndInferResult::ChainFact(stored))
            }
            Fact::OrFact(or_fact) => {
                let stored = self.store_or_fact(or_fact)?;
                Ok(StoreFactAndInferResult::OrFact(stored))
            }
            Fact::ExistFact(_)
            | Fact::ForallFact(_)
            | Fact::ForallFactWithIff(_)
            | Fact::NotForall(_) => {
                let fact_id = fact.fact_id();
                self.top_exec_env_mut()
                    .facts
                    .record_fact(fact_id, fact.clone());
                Ok(StoreFactAndInferResult::RecordedFact { fact_id })
            }
        }
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

    // Chain: record whole, store adjacent edges, then optional transitive closures.
    // Example: `a < b < c` → adjacent a<b, b<c, then BuiltinNumericOrder ⇒ a<c.
    // `a < b > c` → adjacent only (closures empty).
    fn store_chain_fact(&mut self, chain_fact: &ChainFact) -> RuntimeResult<StoreChainFactResult> {
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

        let transitive_closures = self.store_chain_transitive_closures(chain_fact, &adjacent)?;
        Ok(StoreChainFactResult {
            whole_fact_id,
            fact: chain_fact.clone(),
            adjacent,
            transitive_closures,
        })
    }

    pub fn store_atomic_fact(&mut self, atomic_fact: &AtomicFact) -> RuntimeResult<Vec<FactId>> {
        match atomic_fact {
            AtomicFact::EqualFact(equal_fact) => {
                let fact_id = equal_fact.fact_id;
                let env = self.top_exec_env_mut();
                env.facts.known_equality.store(equal_fact);
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

fn chain_line_file(chain_fact: &ChainFact) -> LineFile {
    chain_fact
        .line_file
        .clone()
        .unwrap_or_else(|| LineFile::new(0, RealOrVirtualPath::Eval))
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum OrderEdge {
    Eq,
    Le,
    Lt,
    Ge,
    Gt,
}

impl Runtime {
    fn store_chain_transitive_closures(
        &mut self,
        chain_fact: &ChainFact,
        adjacent: &[StoreChainAdjacentResult],
    ) -> RuntimeResult<Vec<StoreChainTransitiveClosureResult>> {
        if adjacent.len() < 2 {
            return Ok(Vec::new());
        }

        if chain_props_all_equal(&chain_fact.prop_names) {
            return self.store_builtin_equality_closures(chain_fact, adjacent);
        }

        if let Some(edges) = chain_order_edges(&chain_fact.prop_names) {
            let has_up = edges
                .iter()
                .any(|e| matches!(e, OrderEdge::Le | OrderEdge::Lt));
            let has_down = edges
                .iter()
                .any(|e| matches!(e, OrderEdge::Ge | OrderEdge::Gt));
            if has_up && has_down {
                return Ok(Vec::new());
            }
            if has_up || has_down {
                return self.store_builtin_numeric_order_closures(
                    chain_fact,
                    adjacent,
                    &edges,
                    has_up,
                );
            }
        }

        if let Some(prop_name) = chain_uniform_prop(&chain_fact.prop_names) {
            if self.prop_is_known_transitive(&prop_name) {
                return self.store_known_transitive_closures(chain_fact, adjacent, prop_name);
            }
        }

        Ok(Vec::new())
    }

    fn store_builtin_equality_closures(
        &mut self,
        chain_fact: &ChainFact,
        _adjacent: &[StoreChainAdjacentResult],
    ) -> RuntimeResult<Vec<StoreChainTransitiveClosureResult>> {
        let line_file = chain_line_file(chain_fact);
        let mut closures = Vec::new();
        for start in 0..chain_fact.objs.len() {
            for end in start + 2..chain_fact.objs.len() {
                let conclusion = self.atomic_from_prop(
                    AtomicName::Plain {
                        name: EQUAL.to_string(),
                    },
                    vec![chain_fact.objs[start].clone(), chain_fact.objs[end].clone()],
                    true,
                    line_file.clone(),
                )?;
                let conclusion_fact_id = conclusion.fact_id();
                self.store_atomic_fact(&conclusion)?;
                closures.push(StoreChainTransitiveClosureResult {
                    cite: ChainTransitiveCite::BuiltinEquality,
                    start_object_index: start,
                    end_object_index: end,
                    premise_edge_indexes: (start..end).collect(),
                    conclusion,
                    conclusion_fact_id,
                });
            }
        }
        Ok(closures)
    }

    fn store_builtin_numeric_order_closures(
        &mut self,
        chain_fact: &ChainFact,
        _adjacent: &[StoreChainAdjacentResult],
        edges: &[OrderEdge],
        has_up: bool,
    ) -> RuntimeResult<Vec<StoreChainTransitiveClosureResult>> {
        let line_file = chain_line_file(chain_fact);
        let mut closures = Vec::new();
        for start in 0..chain_fact.objs.len() {
            for end in start + 2..chain_fact.objs.len() {
                let path = &edges[start..end];
                if path.iter().any(|edge| *edge == OrderEdge::Eq) {
                    continue;
                }
                let path_is_strict = path
                    .iter()
                    .any(|edge| matches!(edge, OrderEdge::Lt | OrderEdge::Gt));
                let op = if has_up {
                    if path_is_strict {
                        LESS
                    } else {
                        LESS_EQUAL
                    }
                } else if path_is_strict {
                    GREATER
                } else {
                    GREATER_EQUAL
                };
                let conclusion = self.atomic_from_prop(
                    AtomicName::Plain {
                        name: op.to_string(),
                    },
                    vec![chain_fact.objs[start].clone(), chain_fact.objs[end].clone()],
                    true,
                    line_file.clone(),
                )?;
                let conclusion_fact_id = conclusion.fact_id();
                self.store_atomic_fact(&conclusion)?;
                closures.push(StoreChainTransitiveClosureResult {
                    cite: ChainTransitiveCite::BuiltinNumericOrder,
                    start_object_index: start,
                    end_object_index: end,
                    premise_edge_indexes: (start..end).collect(),
                    conclusion,
                    conclusion_fact_id,
                });
            }
        }
        Ok(closures)
    }

    fn store_known_transitive_closures(
        &mut self,
        chain_fact: &ChainFact,
        _adjacent: &[StoreChainAdjacentResult],
        prop_name: AtomicName,
    ) -> RuntimeResult<Vec<StoreChainTransitiveClosureResult>> {
        let line_file = chain_line_file(chain_fact);
        let mut closures = Vec::new();
        for start in 0..chain_fact.objs.len() {
            for end in start + 2..chain_fact.objs.len() {
                let conclusion = self.atomic_from_prop(
                    prop_name.clone(),
                    vec![chain_fact.objs[start].clone(), chain_fact.objs[end].clone()],
                    true,
                    line_file.clone(),
                )?;
                let conclusion_fact_id = conclusion.fact_id();
                self.store_atomic_fact(&conclusion)?;
                closures.push(StoreChainTransitiveClosureResult {
                    cite: ChainTransitiveCite::KnownTransitive {
                        prop_name: prop_name.clone(),
                    },
                    start_object_index: start,
                    end_object_index: end,
                    premise_edge_indexes: (start..end).collect(),
                    conclusion,
                    conclusion_fact_id,
                });
            }
        }
        Ok(closures)
    }

    fn prop_is_known_transitive(&self, prop: &AtomicName) -> bool {
        for env in self.execution_environments_stack.iter().rev() {
            if let Some(props) = env.prop_rewrite_properties.get(prop) {
                if props
                    .iter()
                    .any(|p| matches!(p, PropRewriteProperty::Transitive))
                {
                    return true;
                }
            }
        }
        false
    }
}

fn chain_props_all_equal(prop_names: &[AtomicName]) -> bool {
    !prop_names.is_empty()
        && prop_names.iter().all(|p| match p {
            AtomicName::Plain { name } => name == EQUAL,
            _ => false,
        })
}

fn chain_uniform_prop(prop_names: &[AtomicName]) -> Option<AtomicName> {
    let first = prop_names.first()?.clone();
    if prop_names.iter().all(|p| p == &first) {
        Some(first)
    } else {
        None
    }
}

fn chain_order_edges(prop_names: &[AtomicName]) -> Option<Vec<OrderEdge>> {
    let mut edges = Vec::with_capacity(prop_names.len());
    for prop in prop_names {
        let AtomicName::Plain { name } = prop else {
            return None;
        };
        let edge = match name.as_str() {
            EQUAL => OrderEdge::Eq,
            LESS_EQUAL => OrderEdge::Le,
            LESS => OrderEdge::Lt,
            GREATER_EQUAL => OrderEdge::Ge,
            GREATER => OrderEdge::Gt,
            _ => return None,
        };
        edges.push(edge);
    }
    Some(edges)
}
