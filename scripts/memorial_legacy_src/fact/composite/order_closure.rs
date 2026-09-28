//! Ordered relation-chain closure and its retained steps.

use crate::prelude::*;
use std::collections::{HashMap, HashSet};

#[derive(Clone, Copy, PartialEq, Eq)]
enum OrderEdge {
    Eq,
    Le,
    Lt,
    Ge,
    Gt,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum ChainPolarity {
    Up,
    Down,
}

struct UnionFind {
    parent: Vec<usize>,
}

pub struct NumericOrderChainClosureStep {
    pub start_object_index: usize,
    pub end_object_index: usize,
    pub premises: Vec<Fact>,
    pub conclusion: AtomicFact,
}

impl UnionFind {
    fn new(n: usize) -> Self {
        UnionFind {
            parent: (0..n).collect(),
        }
    }

    fn find(&mut self, x: usize) -> usize {
        if self.parent[x] != x {
            self.parent[x] = self.find(self.parent[x]);
        }
        self.parent[x]
    }

    fn union(&mut self, a: usize, b: usize) {
        let ra = self.find(a);
        let rb = self.find(b);
        if ra != rb {
            self.parent[rb] = ra;
        }
    }
}

fn order_edge_from_prop(p: &AtomicName) -> Option<OrderEdge> {
    match p.to_string().as_str() {
        EQUAL => Some(OrderEdge::Eq),
        LESS_EQUAL => Some(OrderEdge::Le),
        LESS => Some(OrderEdge::Lt),
        GREATER_EQUAL => Some(OrderEdge::Ge),
        GREATER => Some(OrderEdge::Gt),
        _ => None,
    }
}

fn set_inclusion_edge_from_prop(p: &AtomicName) -> Option<(ChainPolarity, bool)> {
    match p.to_string().as_str() {
        SUBSET => Some((ChainPolarity::Up, false)),
        PROPER_SUBSET => Some((ChainPolarity::Up, true)),
        SUPERSET => Some((ChainPolarity::Down, false)),
        PROPER_SUPERSET => Some((ChainPolarity::Down, true)),
        _ => None,
    }
}

fn dedup_atomic_facts(mut facts: Vec<AtomicFact>) -> Vec<AtomicFact> {
    let mut seen = HashSet::new();
    facts.retain(|f| seen.insert(f.to_string()));
    facts
}

impl ChainFact {
    /// Retain proof-replayable closure steps for mixed strict/weak numeric
    /// order chains. Equality edges use a different semantic transport and
    /// are deliberately excluded from this certificate family.
    pub fn numeric_order_chain_closure_steps_with_runtime(
        &self,
        runtime: &Runtime,
    ) -> Result<Vec<NumericOrderChainClosureStep>, RuntimeError> {
        let adjacent = self.facts(runtime)?;
        let mut edges = Vec::with_capacity(self.prop_names.len());
        for predicate in &self.prop_names {
            let Some(edge) = order_edge_from_prop(predicate) else {
                return Ok(Vec::new());
            };
            edges.push(edge);
        }
        let has_up = edges
            .iter()
            .any(|edge| matches!(edge, OrderEdge::Le | OrderEdge::Lt));
        let has_down = edges
            .iter()
            .any(|edge| matches!(edge, OrderEdge::Ge | OrderEdge::Gt));
        if has_up == has_down {
            return Ok(Vec::new());
        }

        let mut steps = Vec::new();
        for start in 0..self.objs.len() {
            for end in start + 2..self.objs.len() {
                let path = &edges[start..end];
                if path.iter().any(|edge| *edge == OrderEdge::Eq) {
                    continue;
                }
                let path_is_strict = path
                    .iter()
                    .any(|edge| matches!(edge, OrderEdge::Lt | OrderEdge::Gt));
                let conclusion: AtomicFact = if has_up {
                    if path_is_strict {
                        runtime
                            .new_less_fact(
                                self.objs[start].clone(),
                                self.objs[end].clone(),
                                self.line_file.clone(),
                            )
                            .into()
                    } else {
                        runtime
                            .new_less_equal_fact(
                                self.objs[start].clone(),
                                self.objs[end].clone(),
                                self.line_file.clone(),
                            )
                            .into()
                    }
                } else if path_is_strict {
                    runtime
                        .new_greater_fact(
                            self.objs[start].clone(),
                            self.objs[end].clone(),
                            self.line_file.clone(),
                        )
                        .into()
                } else {
                    runtime
                        .new_greater_equal_fact(
                            self.objs[start].clone(),
                            self.objs[end].clone(),
                            self.line_file.clone(),
                        )
                        .into()
                };
                steps.push(NumericOrderChainClosureStep {
                    start_object_index: start,
                    end_object_index: end,
                    premises: adjacent[start..end]
                        .iter()
                        .cloned()
                        .map(Fact::from)
                        .collect(),
                    conclusion,
                });
            }
        }
        Ok(steps)
    }

    pub fn facts_with_order_transitive_closure_with_runtime(
        &self,
        runtime: &Runtime,
    ) -> Result<Vec<AtomicFact>, RuntimeError> {
        let base = self.facts(runtime)?;
        let n = self.objs.len();
        if n < 2 {
            return Ok(base);
        }

        if let Some((polarity, _)) = self
            .prop_names
            .first()
            .and_then(set_inclusion_edge_from_prop)
        {
            let mut inclusion_edges = Vec::with_capacity(self.prop_names.len());
            for prop_name in &self.prop_names {
                let Some(edge) = set_inclusion_edge_from_prop(prop_name) else {
                    return Ok(base);
                };
                if edge.0 != polarity {
                    return Ok(base);
                }
                inclusion_edges.push(edge);
            }

            // Same-direction inclusion chains are transitive, and one strict edge
            // makes every enclosing path strict.
            // Example: `A $subset B $proper_subset C` yields `A $proper_subset C`.
            let mut extra = Vec::new();
            let lf = self.line_file.clone();
            for i in 0..n {
                for j in i + 2..n {
                    let path_is_strict = inclusion_edges[i..j].iter().any(|edge| edge.1);
                    let predicate = match (polarity, path_is_strict) {
                        (ChainPolarity::Up, false) => SUBSET,
                        (ChainPolarity::Up, true) => PROPER_SUBSET,
                        (ChainPolarity::Down, false) => SUPERSET,
                        (ChainPolarity::Down, true) => PROPER_SUPERSET,
                    };
                    extra.push(AtomicFact::to_atomic_fact(
                        runtime,
                        AtomicName::WithoutMod(predicate.to_string()),
                        true,
                        vec![self.objs[i].clone(), self.objs[j].clone()],
                        lf.clone(),
                    )?);
                }
            }

            let mut all = base;
            all.extend(extra);
            return Ok(dedup_atomic_facts(all));
        }

        let mut edges: Vec<OrderEdge> = Vec::with_capacity(self.prop_names.len());
        for p in &self.prop_names {
            let Some(e) = order_edge_from_prop(p) else {
                return Ok(base);
            };
            edges.push(e);
        }

        let mut has_up = false;
        let mut has_down = false;
        for e in &edges {
            match e {
                OrderEdge::Le | OrderEdge::Lt => has_up = true,
                OrderEdge::Ge | OrderEdge::Gt => has_down = true,
                OrderEdge::Eq => {}
            }
        }
        if has_up && has_down {
            return Ok(base);
        }

        let polarity = if has_up {
            ChainPolarity::Up
        } else if has_down {
            ChainPolarity::Down
        } else {
            ChainPolarity::Up
        };

        let mut uf = UnionFind::new(n);
        for (k, e) in edges.iter().enumerate() {
            if *e == OrderEdge::Eq {
                uf.union(k, k + 1);
            }
        }

        let mut quotient: Vec<usize> = Vec::new();
        for i in 0..n {
            if i == 0 || uf.find(i) != uf.find(i - 1) {
                quotient.push(i);
            }
        }

        let mut between_strict: Vec<bool> = Vec::new();
        for k in 0..edges.len() {
            let ca = uf.find(k);
            let cb = uf.find(k + 1);
            if ca != cb {
                let strict = match polarity {
                    ChainPolarity::Up => matches!(edges[k], OrderEdge::Lt),
                    ChainPolarity::Down => matches!(edges[k], OrderEdge::Gt),
                };
                between_strict.push(strict);
            }
        }

        if between_strict.len() + 1 != quotient.len() {
            return Ok(base);
        }

        let lf = self.line_file.clone();
        let mut extra: Vec<AtomicFact> = Vec::new();

        let mut members: HashMap<usize, Vec<usize>> = HashMap::new();
        for i in 0..n {
            members.entry(uf.find(i)).or_default().push(i);
        }
        for mut indexes in members.into_values() {
            if indexes.len() < 2 {
                continue;
            }
            indexes.sort_unstable();
            for ii in 0..indexes.len() {
                for jj in ii + 1..indexes.len() {
                    let i = indexes[ii];
                    let j = indexes[jj];
                    extra.push(
                        runtime
                            .new_equal_fact(self.objs[i].clone(), self.objs[j].clone(), lf.clone())
                            .into(),
                    );
                }
            }
        }

        for qi in 0..quotient.len() {
            for qj in qi + 1..quotient.len() {
                let path_strict = between_strict[qi..qj].iter().any(|&s| s);
                let left = self.objs[quotient[qi]].clone();
                let right = self.objs[quotient[qj]].clone();
                let f = match polarity {
                    ChainPolarity::Up => {
                        if path_strict {
                            runtime.new_less_fact(left, right, lf.clone()).into()
                        } else {
                            runtime.new_less_equal_fact(left, right, lf.clone()).into()
                        }
                    }
                    ChainPolarity::Down => {
                        if path_strict {
                            runtime.new_greater_fact(left, right, lf.clone()).into()
                        } else {
                            runtime
                                .new_greater_equal_fact(left, right, lf.clone())
                                .into()
                        }
                    }
                };
                extra.push(f);
            }
        }

        let mut all = base;
        all.extend(extra);
        Ok(dedup_atomic_facts(all))
    }

    /// Compatibility wrapper for callers that do not yet own a runtime.
    /// Production code should pass its runtime explicitly.
    #[deprecated(note = "pass the owning Runtime explicitly")]
    pub fn numeric_order_chain_closure_steps(
        &self,
    ) -> Result<Vec<NumericOrderChainClosureStep>, RuntimeError> {
        self.numeric_order_chain_closure_steps_with_runtime(&Runtime::default())
    }

    /// Compatibility wrapper for callers that do not yet own a runtime.
    /// Production code should pass its runtime explicitly.
    #[deprecated(note = "pass the owning Runtime explicitly")]
    pub fn facts_with_order_transitive_closure(&self) -> Result<Vec<AtomicFact>, RuntimeError> {
        self.facts_with_order_transitive_closure_with_runtime(&Runtime::default())
    }
}

#[cfg(test)]
#[path = "../../../tests/unit/fact/composite/order_closure.rs"]
mod tests;
