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

fn order_edge_from_prop(p: &IdentifierOrIdentifierWithMod) -> Option<OrderEdge> {
    match p.to_string().as_str() {
        EQUAL => Some(OrderEdge::Eq),
        LESS_EQUAL => Some(OrderEdge::Le),
        LESS => Some(OrderEdge::Lt),
        GREATER_EQUAL => Some(OrderEdge::Ge),
        GREATER => Some(OrderEdge::Gt),
        _ => None,
    }
}

fn dedup_atomic_facts(mut facts: Vec<AtomicFact>) -> Vec<AtomicFact> {
    let mut seen = HashSet::new();
    facts.retain(|f| seen.insert(f.to_string()));
    facts
}

impl ChainFact {
    pub fn facts_with_order_transitive_closure(&self) -> Result<Vec<AtomicFact>, RuntimeError> {
        let base = self.facts()?;
        let n = self.objs.len();
        if n < 2 {
            return Ok(base);
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
        for mut idxs in members.into_values() {
            if idxs.len() < 2 {
                continue;
            }
            idxs.sort_unstable();
            for ii in 0..idxs.len() {
                for jj in ii + 1..idxs.len() {
                    let i = idxs[ii];
                    let j = idxs[jj];
                    extra.push(
                        EqualFact::new(self.objs[i].clone(), self.objs[j].clone(), lf.clone())
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
                            LessFact::new(left, right, lf.clone()).into()
                        } else {
                            LessEqualFact::new(left, right, lf.clone()).into()
                        }
                    }
                    ChainPolarity::Down => {
                        if path_strict {
                            GreaterFact::new(left, right, lf.clone()).into()
                        } else {
                            GreaterEqualFact::new(left, right, lf.clone()).into()
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
}
