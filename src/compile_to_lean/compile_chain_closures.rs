use crate::compile_to_lean::compile_compound_fact::chain_edge;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;
use crate::store_fact_and_infer::helper::{chain_order_edges, OrderEdge};
use crate::store_fact_and_infer::{ChainTransitiveCite, InferFactResult};

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_chain_closures(
        &self,
        store: &StoreFactAndInferResult,
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        let (StoreFactResult::ChainFact(stored), Some(InferFactResult::ChainFact(inferred))) =
            (&store.store, &store.infer)
        else {
            return Err(LeanCompileError::unsupported("Chain/ClosureFamily"));
        };
        let Some(edges) = chain_order_edges(&stored.fact.prop_names) else {
            if inferred.transitive_closures.is_empty() {
                return Ok(Vec::new());
            }
            return Err(LeanCompileError::unsupported(
                "Chain/RegisteredTransitivity",
            ));
        };
        let mut declarations = Vec::new();
        for (index, closure) in inferred.transitive_closures.iter().enumerate() {
            let start = closure.start_object_index;
            let end = closure.end_object_index;
            if end <= start + 1
                || end >= stored.fact.objs.len()
                || closure.premise_edge_indexes != (start..end).collect::<Vec<_>>()
            {
                return Err(LeanCompileError::new(
                    "Chain/ClosureIndexes",
                    "The closure omits, reorders or changes its original contiguous edge path.",
                ));
            }
            let path = &edges[start..end];
            let equality = path.iter().all(|edge| *edge == OrderEdge::Eq);
            let up = path
                .iter()
                .any(|edge| matches!(edge, OrderEdge::Lt | OrderEdge::Le));
            let down = path
                .iter()
                .any(|edge| matches!(edge, OrderEdge::Gt | OrderEdge::Ge));
            if up && down {
                return Err(LeanCompileError::unsupported("Chain/ClosureDirection"));
            }
            match &closure.cite {
                ChainTransitiveCite::BuiltinEquality if equality => {}
                ChainTransitiveCite::BuiltinNumericOrder if !equality && (up || down) => {}
                ChainTransitiveCite::KnownTransitive { .. } => {
                    return Err(LeanCompileError::unsupported(
                        "Chain/RegisteredTransitivity",
                    ))
                }
                _ => {
                    return Err(LeanCompileError::new(
                        "Chain/ClosureRule",
                        "The selected numeric closure does not match its captured relation path.",
                    ))
                }
            }
            let captured = &closure.derived;
            let derived = &captured.store;
            let StoreFactResult::AtomicFact(actual) = derived else {
                return Err(LeanCompileError::unsupported("Chain/ClosureConclusion"));
            };
            let strict = path
                .iter()
                .any(|edge| matches!(edge, OrderEdge::Lt | OrderEdge::Gt));
            let relation = if equality {
                "="
            } else if down {
                if strict {
                    ">"
                } else {
                    ">="
                }
            } else if strict {
                "<"
            } else {
                "<="
            };
            let expected_chain = ChainFact {
                fact_id: stored.fact.fact_id,
                objs: vec![
                    stored.fact.objs[start].clone(),
                    stored.fact.objs[end].clone(),
                ],
                prop_names: vec![AtomicName::Plain {
                    name: relation.into(),
                }],
                line_file: stored.fact.line_file.clone(),
            };
            if actual.fact_id != actual.fact.fact_id()
                || actual.fact != chain_edge(&expected_chain, 0, actual.fact_id)?
            {
                return Err(LeanCompileError::new(
                    "Chain/ClosureSubject",
                    "The captured closure has other endpoints, orientation, relation or identity.",
                ));
            }
            let fact = Fact::AtomicFact(actual.fact.clone());
            let prior = SourcePosition {
                before: inferred.adjacent_infers.len() + index,
                ..*position
            };
            if self.resolve_fact(actual.fact_id, &prior)? != fact {
                return Err(LeanCompileError::new(
                    "Chain/ClosureIdentity",
                    "The original closure FactId resolves to another subject.",
                ));
            }
            let current = SourcePosition::new(Some(&prior), SourceOwner::ChainClosure(closure), 0);
            self.compile_fact_wd(&captured.well_defined, &fact, &current)?;
            self.validate_store(derived, &fact)?;
            let formed = SourcePosition::new(
                Some(&current),
                SourceOwner::FactWD(&captured.well_defined),
                usize::MAX,
            );
            let edge_indexes: Vec<_> = if down && !equality {
                (start..end).rev().collect()
            } else {
                (start..end).collect()
            };
            let mut first = true;
            let mut prefix_kind = OrderEdge::Eq;
            let mut prefix_proof = String::new();
            let start_index = if down && !equality { end } else { start };
            for edge_index in edge_indexes {
                let edge = edges[edge_index];
                let reverse = down && !equality;
                let (middle, finish) = if reverse {
                    (edge_index + 1, edge_index)
                } else {
                    (edge_index, edge_index + 1)
                };
                let kind = match edge {
                    OrderEdge::Ge => OrderEdge::Le,
                    OrderEdge::Gt => OrderEdge::Lt,
                    other => other,
                };
                let id = stored.adjacent[edge_index].fact_id;
                let (_, mut checked) = self.cited_fact_reference(id, &formed)?;
                if reverse && kind == OrderEdge::Eq {
                    checked = format!("(Eq.symm {checked})");
                }
                if first {
                    first = false;
                    prefix_kind = kind;
                    prefix_proof = checked;
                    continue;
                }
                let a = self.compile_object_reference(&stored.fact.objs[start_index], &formed)?;
                let b = self.compile_object_reference(&stored.fact.objs[middle], &formed)?;
                let c = self.compile_object_reference(&stored.fact.objs[finish], &formed)?;
                prefix_proof = match (prefix_kind, kind) {
                    (OrderEdge::Eq, OrderEdge::Eq) => format!("(Eq.trans {prefix_proof} {checked})"),
                    (OrderEdge::Eq, OrderEdge::Le) => format!("(Litex.leOfSame {b} {a} {c} {c} (Eq.symm {prefix_proof}) (Litex.sameRefl {c}) {checked})"),
                    (OrderEdge::Eq, OrderEdge::Lt) => format!("(Litex.ltOfSame {b} {a} {c} {c} (Eq.symm {prefix_proof}) (Litex.sameRefl {c}) {checked})"),
                    (OrderEdge::Le, OrderEdge::Eq) => format!("(Litex.leOfSame {a} {a} {b} {c} (Litex.sameRefl {a}) {checked} {prefix_proof})"),
                    (OrderEdge::Lt, OrderEdge::Eq) => format!("(Litex.ltOfSame {a} {a} {b} {c} (Litex.sameRefl {a}) {checked} {prefix_proof})"),
                    (OrderEdge::Le, OrderEdge::Le) => format!("(Litex.leTrans {a} {b} {c} {prefix_proof} {checked})"),
                    (OrderEdge::Le, OrderEdge::Lt) => format!("(Litex.leLtTrans {a} {b} {c} {prefix_proof} {checked})"),
                    (OrderEdge::Lt, OrderEdge::Le) => format!("(Litex.ltLeTrans {a} {b} {c} {prefix_proof} {checked})"),
                    (OrderEdge::Lt, OrderEdge::Lt) => format!("(Litex.ltTrans {a} {b} {c} {prefix_proof} {checked})"),
                    _ => return Err(LeanCompileError::unsupported("Chain/ClosureDirection")),
                };
                prefix_kind = if prefix_kind == OrderEdge::Lt || kind == OrderEdge::Lt {
                    OrderEdge::Lt
                } else if prefix_kind == OrderEdge::Le || kind == OrderEdge::Le {
                    OrderEdge::Le
                } else {
                    OrderEdge::Eq
                };
            }
            let compiled = (self.fact_proposition(&fact, &formed)?, prefix_proof);
            declarations.push(self.emit_internal_fact(&fact, &compiled, &prior));
        }
        Ok(declarations)
    }
}
