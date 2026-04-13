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
    pub fn facts_with_order_transitive_closure(&self) -> Result<Vec<AtomicFact>, RuntimeErrorStruct> {
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
            let rep = idxs[0];
            for &j in idxs.iter().skip(1) {
                extra.push(EqualFact::new(
                    self.objs[rep].clone(),
                    self.objs[j].clone(),
                    lf.clone(),
                ).into());
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
                            GreaterEqualFact::new(
                                left, right, lf.clone(),
                            ).into()
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

#[cfg(test)]
mod tests {
    use super::*;

    fn id(name: &str) -> Obj {
        Identifier::mk(name.to_string())
    }

    fn prop(s: &str) -> IdentifierOrIdentifierWithMod {
        IdentifierOrIdentifierWithMod::Identifier(Identifier::new(s.to_string()))
    }

    #[test]
    fn le_eq_lt_chain_adds_transitive_facts() {
        let lf = default_line_file();
        let chain = ChainFact::new(
            vec![id("a"), id("b"), id("c"), id("d")],
            vec![prop("<="), prop("="), prop("<")],
            lf.clone(),
        );
        let facts = chain.facts_with_order_transitive_closure().unwrap();
        let displayed: Vec<_> = facts.iter().map(|f| f.to_string()).collect();
        assert!(displayed.iter().any(|s| s.contains("a") && s.contains("d")));
        assert!(
            facts.len() >= 5,
            "expected transitive closure beyond three adjacent facts, got {:?}",
            displayed
        );
    }

    #[test]
    fn mixed_up_down_chain_skips_closure_beyond_base() {
        let lf = default_line_file();
        let chain = ChainFact::new(
            vec![id("a"), id("b"), id("c")],
            vec![prop("<="), prop(">")],
            lf,
        );
        let facts = chain.facts_with_order_transitive_closure().unwrap();
        assert_eq!(facts.len(), 2);
    }

    #[test]
    fn ge_eq_gt_chain_adds_transitive_greater_facts() {
        let lf = default_line_file();
        let chain = ChainFact::new(
            vec![id("d"), id("c"), id("b"), id("a")],
            vec![prop(">="), prop("="), prop(">")],
            lf,
        );
        let facts = chain.facts_with_order_transitive_closure().unwrap();
        let displayed: Vec<_> = facts.iter().map(|f| f.to_string()).collect();
        assert!(displayed.iter().any(|s| s.contains("d") && s.contains("a")));
        assert!(facts.len() >= 5);
    }
}
