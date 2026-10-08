use crate::ast::fact::{ChainFact, Fact};
use crate::ast::names::AtomicName;
use crate::exec_env::exec_env::PropRewriteProperty;
use crate::parse::keywords::{EQUAL, GREATER, GREATER_EQUAL, LESS, LESS_EQUAL};
use crate::runtime::{Runtime, RuntimeResult};
use crate::store_fact_and_infer::helper::{
    chain_line_file, chain_order_edges, chain_props_all_equal, chain_uniform_prop, OrderEdge,
};
use crate::store_fact_and_infer::{ChainTransitiveCite, InferChainTransitiveClosureResult};

impl Runtime {
    // Transitive closures from a stored chain (equality / numeric order / known transitive).
    // Example: `a = b = c` stores BuiltinEquality conclusion `a = c`.
    pub(super) fn infer_chain_transitive_closures(
        &mut self,
        chain_fact: &ChainFact,
        adjacent_len: usize,
        verify_state: crate::execute::execute_fact_stmt::VerifyState,
    ) -> RuntimeResult<Vec<InferChainTransitiveClosureResult>> {
        if adjacent_len < 2 {
            return Ok(Vec::new());
        }

        if chain_props_all_equal(&chain_fact.prop_names) {
            return self.infer_builtin_equality_closures(chain_fact, verify_state);
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
                return self.infer_builtin_numeric_order_closures(
                    chain_fact,
                    &edges,
                    has_up,
                    verify_state,
                );
            }
        }

        if let Some(prop_name) = chain_uniform_prop(&chain_fact.prop_names) {
            if self.prop_is_known_transitive(&prop_name) {
                return self.infer_known_transitive_closures(chain_fact, prop_name, verify_state);
            }
        }

        Ok(Vec::new())
    }

    fn infer_builtin_equality_closures(
        &mut self,
        chain_fact: &ChainFact,
        verify_state: crate::execute::execute_fact_stmt::VerifyState,
    ) -> RuntimeResult<Vec<InferChainTransitiveClosureResult>> {
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
                let derived =
                    Box::new(self.store_inferred_fact_and_infer(
                        &Fact::AtomicFact(conclusion),
                        verify_state,
                    )?);
                closures.push(InferChainTransitiveClosureResult {
                    cite: ChainTransitiveCite::BuiltinEquality,
                    start_object_index: start,
                    end_object_index: end,
                    premise_edge_indexes: (start..end).collect(),
                    derived,
                });
            }
        }
        Ok(closures)
    }

    fn infer_builtin_numeric_order_closures(
        &mut self,
        chain_fact: &ChainFact,
        edges: &[OrderEdge],
        has_up: bool,
        verify_state: crate::execute::execute_fact_stmt::VerifyState,
    ) -> RuntimeResult<Vec<InferChainTransitiveClosureResult>> {
        let line_file = chain_line_file(chain_fact);
        let mut closures = Vec::new();
        for start in 0..chain_fact.objs.len() {
            for end in start + 2..chain_fact.objs.len() {
                let path = &edges[start..end];
                // Equality preserves the direction of the checked order edges.
                // For example, `a >= b = c >= d` entails `a >= d`.
                // A purely equal subpath still entails equality, even inside
                // a longer order chain: `a = b = c < d` entails `a = c`.
                let path_is_equality = path.iter().all(|edge| *edge == OrderEdge::Eq);
                let path_is_strict = path
                    .iter()
                    .any(|edge| matches!(edge, OrderEdge::Lt | OrderEdge::Gt));
                let op = if path_is_equality {
                    EQUAL
                } else if has_up {
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
                let derived =
                    Box::new(self.store_inferred_fact_and_infer(
                        &Fact::AtomicFact(conclusion),
                        verify_state,
                    )?);
                closures.push(InferChainTransitiveClosureResult {
                    cite: if path_is_equality {
                        ChainTransitiveCite::BuiltinEquality
                    } else {
                        ChainTransitiveCite::BuiltinNumericOrder
                    },
                    start_object_index: start,
                    end_object_index: end,
                    premise_edge_indexes: (start..end).collect(),
                    derived,
                });
            }
        }
        Ok(closures)
    }

    fn infer_known_transitive_closures(
        &mut self,
        chain_fact: &ChainFact,
        prop_name: AtomicName,
        verify_state: crate::execute::execute_fact_stmt::VerifyState,
    ) -> RuntimeResult<Vec<InferChainTransitiveClosureResult>> {
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
                let derived =
                    Box::new(self.store_inferred_fact_and_infer(
                        &Fact::AtomicFact(conclusion),
                        verify_state,
                    )?);
                closures.push(InferChainTransitiveClosureResult {
                    cite: ChainTransitiveCite::KnownTransitive {
                        prop_name: prop_name.clone(),
                    },
                    start_object_index: start,
                    end_object_index: end,
                    premise_edge_indexes: (start..end).collect(),
                    derived,
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
