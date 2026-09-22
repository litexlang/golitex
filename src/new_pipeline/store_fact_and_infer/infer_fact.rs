use super::helper::{
    chain_line_file, chain_order_edges, chain_props_all_equal, chain_uniform_prop,
    flatten_def_prop_params, OrderEdge,
};
use super::store_fact_and_infer_result::{
    ChainTransitiveCite, InferFactResult, StoreChainAdjacentResult,
    StoreChainTransitiveClosureResult, StoreExistFactResult,
};
use crate::new_pipeline::ast::fact::{
    AtomicFact, ChainFact, EqualFact, Fact, InFact, IsCartFact, IsTupleFact, NormalAtomicFact,
    NotForallFact,
};
use crate::new_pipeline::ast::names::AtomicName;
use crate::new_pipeline::ast::obj::{Cart, CartDim, Number, Obj, Tuple, TupleDim};
use crate::new_pipeline::exec_env::exec_env::PropRewriteProperty;
use crate::new_pipeline::parse::keywords::{
    EQUAL, GREATER, GREATER_EQUAL, LESS, LESS_EQUAL,
};
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // Derive routine consequences from an already-stored fact; store each new fact.
    // Example: after storing `a $in {x R: x > 0}`, infer also stores `a $in R` and `a > 0`.
    pub fn infer_fact(&mut self, fact: &Fact) -> RuntimeResult<InferFactResult> {
        match fact {
            Fact::AtomicFact(atomic) => {
                self.infer_atomic_fact(atomic)?;
                Ok(InferFactResult::Empty)
            }
            Fact::AndFact(and_fact) => {
                for atomic in &and_fact.facts {
                    self.infer_atomic_fact(atomic)?;
                }
                Ok(InferFactResult::Empty)
            }
            Fact::ChainFact(chain_fact) => {
                let adjacent_atomics = self.chain_adjacent_atomics(chain_fact)?;
                for atomic in &adjacent_atomics {
                    self.infer_atomic_fact(atomic)?;
                }
                let mut adjacent = Vec::with_capacity(adjacent_atomics.len());
                for (edge_index, atomic) in adjacent_atomics.into_iter().enumerate() {
                    adjacent.push(StoreChainAdjacentResult {
                        edge_index,
                        fact_id: atomic.fact_id(),
                        fact: atomic,
                    });
                }
                let transitive_closures =
                    self.infer_chain_transitive_closures(chain_fact, &adjacent)?;
                Ok(InferFactResult::ChainFact {
                    transitive_closures,
                })
            }
            Fact::OrFact(_) => Ok(InferFactResult::Empty),
            Fact::ExistFact(_) | Fact::ExistUniqueFact(_) | Fact::NotExistFact(_) => {
                Ok(InferFactResult::Empty)
            }
            Fact::NotForall(not_forall) => {
                let derived_exist = self.infer_not_forall_fact(not_forall)?;
                Ok(InferFactResult::NotForallFact { derived_exist })
            }
            Fact::ForallFact(_) | Fact::ForallFactWithIff(_) => Ok(InferFactResult::Empty),
        }
    }

    fn infer_atomic_fact(&mut self, atomic_fact: &AtomicFact) -> RuntimeResult<()> {
        if let AtomicFact::EqualFact(equal_fact) = atomic_fact {
            self.infer_cart_tuple_shape_from_stored_equal_fact(equal_fact)?;
        }
        if let AtomicFact::NormalAtomicFact(normal) = atomic_fact {
            self.infer_prop_definition_iff_consequences(normal)?;
        }
        if let AtomicFact::InFact(in_fact) = atomic_fact {
            self.infer_projections_from_stored_in_fact(in_fact)?;
        }
        Ok(())
    }

    // Knowing `$P(args)` also stores the prop's defining iff facts (one layer).
    // Example: `prop same(x set, y set): x = y` and store `$same(a, b)` → also store `a = b`.
    fn infer_prop_definition_iff_consequences(
        &mut self,
        normal: &NormalAtomicFact,
    ) -> RuntimeResult<()> {
        let name = normal.predicate.local_name();
        if self.def_abstract_prop_visible_in_stack(name).is_some() {
            return Ok(());
        }
        let Some(definition) = self.def_prop_visible_in_stack(name) else {
            return Ok(());
        };
        if definition.iff_facts.is_empty() {
            return Ok(());
        }
        let definition = definition.clone();
        let flat = flatten_def_prop_params(&definition.typed_parameters);
        if flat.len() != normal.body.len() {
            return Ok(());
        }
        let mut subst = std::collections::HashMap::new();
        for (param, arg) in flat.iter().zip(normal.body.iter()) {
            subst.insert(param.id, arg.clone());
        }
        for iff_fact in &definition.iff_facts {
            let Ok(instantiated) = self.inst_fact(iff_fact, &subst) else {
                continue;
            };
            match instantiated {
                Fact::AtomicFact(atomic) => {
                    // Index only — avoid cyclic re-expansion through nested NormalAtomic.
                    self.store_atomic_fact(&atomic)?;
                }
                other => {
                    let _ = self.store_fact_and_infer(&other)?;
                }
            }
        }
        Ok(())
    }

    // NotForall: De Morgan counterexample exist into known_exist.
    // Example: `not forall x R: x > 0` → also store `exist x R st {not x > 0}`.
    fn infer_not_forall_fact(
        &mut self,
        not_forall: &NotForallFact,
    ) -> RuntimeResult<StoreExistFactResult> {
        let Some(derived_exist) = self.not_forall_to_counterexample_exist(not_forall)? else {
            return Err(crate::new_pipeline::runtime::RuntimeError::InternalBug(
                "infer not forall: cannot negate body into exist counterexample".to_string(),
            ));
        };
        self.store_exist_fact(&derived_exist)
    }

    fn infer_chain_transitive_closures(
        &mut self,
        chain_fact: &ChainFact,
        adjacent: &[StoreChainAdjacentResult],
    ) -> RuntimeResult<Vec<StoreChainTransitiveClosureResult>> {
        if adjacent.len() < 2 {
            return Ok(Vec::new());
        }

        if chain_props_all_equal(&chain_fact.prop_names) {
            return self.infer_builtin_equality_closures(chain_fact);
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
                return self.infer_builtin_numeric_order_closures(chain_fact, &edges, has_up);
            }
        }

        if let Some(prop_name) = chain_uniform_prop(&chain_fact.prop_names) {
            if self.prop_is_known_transitive(&prop_name) {
                return self.infer_known_transitive_closures(chain_fact, prop_name);
            }
        }

        Ok(Vec::new())
    }

    fn infer_builtin_equality_closures(
        &mut self,
        chain_fact: &ChainFact,
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
                let _ = self.store_fact_and_infer(&Fact::AtomicFact(conclusion.clone()))?;
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

    fn infer_builtin_numeric_order_closures(
        &mut self,
        chain_fact: &ChainFact,
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
                let _ = self.store_fact_and_infer(&Fact::AtomicFact(conclusion.clone()))?;
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

    fn infer_known_transitive_closures(
        &mut self,
        chain_fact: &ChainFact,
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
                let _ = self.store_fact_and_infer(&Fact::AtomicFact(conclusion.clone()))?;
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

    // When storing `x $in S`, also store definitional projections of S:
    // - SetBuilder: `x $in param_set` and each instantiated defining fact
    // - PowerSet: `x $subset base`
    // - Name / template equal to either of the above: resolve via known equality
    // Example: trust `a $in {x R: x > 0}` also stores `a $in R` and `a > 0`.
    fn infer_projections_from_stored_in_fact(&mut self, in_fact: &InFact) -> RuntimeResult<()> {
        if let Some(builder) = self.resolve_set_builder_for_membership_projection(&in_fact.set) {
            let base_in = AtomicFact::InFact(InFact {
                fact_id: self.ids.allocate_fact_id(),
                element: in_fact.element.clone(),
                set: builder.param_set.as_ref().clone(),
                line_file: in_fact.line_file.clone(),
            });
            self.store_atomic_fact(&base_in)?;
            let mut subst = std::collections::HashMap::new();
            subst.insert(builder.param_binding.id, in_fact.element.clone());
            for defining in &builder.facts {
                let Ok(qf) = self.inst_quantifier_free_fact(defining, &subst) else {
                    continue;
                };
                let projected = crate::new_pipeline::instantiate::quantifier_free_fact_to_fact(qf);
                match projected {
                    Fact::AtomicFact(atomic) => {
                        self.store_atomic_fact(&atomic)?;
                    }
                    other => {
                        let _ = self.store_fact_and_infer(&other)?;
                    }
                }
            }
            return Ok(());
        }
        if let Some(base) = self.resolve_power_set_base_for_membership_projection(&in_fact.set) {
            let subset = AtomicFact::SubsetFact(crate::new_pipeline::ast::fact::SubsetFact {
                fact_id: self.ids.allocate_fact_id(),
                left: in_fact.element.clone(),
                right: base,
                line_file: in_fact.line_file.clone(),
            });
            self.store_atomic_fact(&subset)?;
        }
        Ok(())
    }

    fn resolve_set_builder_for_membership_projection(
        &self,
        set: &Obj,
    ) -> Option<crate::new_pipeline::ast::obj::SetBuilder> {
        if let Obj::SetBuilder(builder) = set {
            return Some(builder.clone());
        }
        let adjacency = self.visible_equivalence_class_adjacency();
        let neighbors = adjacency.get(&set.ir())?;
        for (_peer_key, equal_fact) in neighbors.iter() {
            let peer = if equal_fact.left.ir() == set.ir() {
                &equal_fact.right
            } else {
                &equal_fact.left
            };
            if let Obj::SetBuilder(builder) = peer {
                return Some(builder.clone());
            }
        }
        None
    }

    fn resolve_power_set_base_for_membership_projection(&self, set: &Obj) -> Option<Obj> {
        if let Obj::PowerSet(power) = set {
            return Some(power.set.as_ref().clone());
        }
        let adjacency = self.visible_equivalence_class_adjacency();
        let neighbors = adjacency.get(&set.ir())?;
        for (_peer_key, equal_fact) in neighbors.iter() {
            let peer = if equal_fact.left.ir() == set.ir() {
                &equal_fact.right
            } else {
                &equal_fact.left
            };
            if let Obj::PowerSet(power) = peer {
                return Some(power.set.as_ref().clone());
            }
        }
        None
    }

    // Infer: equality with a literal cart/tuple side records shape facts on the other side.
    // Condition: store `s = cart(A, B)` or `t = (1, 2)` (exactly one usable literal side).
    // After: `$is_cart(s)`, `cart_dim(s) = 2`; or `$is_tuple(t)`, `tuple_dim(t) = 2`.
    // Example: `have s set = cart(R, R)` then `$is_cart(s)` and `cart_dim(s) = 2` are known.
    fn infer_cart_tuple_shape_from_stored_equal_fact(
        &mut self,
        equal_fact: &EqualFact,
    ) -> RuntimeResult<()> {
        if let Obj::Cart(cart) = &equal_fact.left {
            self.infer_equal_fact_cart_from_known_side(cart, &equal_fact.right, equal_fact)?;
        }
        if let Obj::Cart(cart) = &equal_fact.right {
            self.infer_equal_fact_cart_from_known_side(cart, &equal_fact.left, equal_fact)?;
        }
        if let Obj::Tuple(tuple) = &equal_fact.left {
            self.infer_equal_fact_tuple_from_known_side(tuple, &equal_fact.right, equal_fact)?;
        } else if let Obj::Tuple(tuple) = &equal_fact.right {
            self.infer_equal_fact_tuple_from_known_side(tuple, &equal_fact.left, equal_fact)?;
        }
        Ok(())
    }

    // Infer: `target = cart(...)` ⇒ `$is_cart(target)` and `cart_dim(target) = n`.
    // Example: store `s = cart(R, Z)` also stores `$is_cart(s)` and `cart_dim(s) = 2`.
    fn infer_equal_fact_cart_from_known_side(
        &mut self,
        known_cart: &Cart,
        target: &Obj,
        equal_fact: &EqualFact,
    ) -> RuntimeResult<()> {
        let is_cart = AtomicFact::IsCartFact(IsCartFact {
            fact_id: self.ids.allocate_fact_id(),
            set: target.clone(),
            line_file: equal_fact.line_file.clone(),
        });
        self.store_atomic_fact(&is_cart)?;

        let dim_equal = AtomicFact::EqualFact(EqualFact {
            fact_id: self.ids.allocate_fact_id(),
            left: Obj::CartDim(CartDim {
                set: Box::new(target.clone()),
            }),
            right: Obj::Number(Number {
                normalized_value: known_cart.args.len().to_string(),
            }),
            line_file: equal_fact.line_file.clone(),
        });
        self.store_atomic_fact(&dim_equal)?;
        Ok(())
    }

    // Infer: `target = (…)` with len >= 2 ⇒ `$is_tuple(target)` and `tuple_dim(target) = n`.
    // Example: store `t = (1, 2)` also stores `$is_tuple(t)` and `tuple_dim(t) = 2`.
    fn infer_equal_fact_tuple_from_known_side(
        &mut self,
        known_tuple: &Tuple,
        target: &Obj,
        equal_fact: &EqualFact,
    ) -> RuntimeResult<()> {
        if known_tuple.args.len() < 2 {
            return Ok(());
        }
        let is_tuple = AtomicFact::IsTupleFact(IsTupleFact {
            fact_id: self.ids.allocate_fact_id(),
            set: target.clone(),
            line_file: equal_fact.line_file.clone(),
        });
        self.store_atomic_fact(&is_tuple)?;

        let dim_equal = AtomicFact::EqualFact(EqualFact {
            fact_id: self.ids.allocate_fact_id(),
            left: Obj::TupleDim(TupleDim {
                arg: Box::new(target.clone()),
            }),
            right: Obj::Number(Number {
                normalized_value: known_tuple.args.len().to_string(),
            }),
            line_file: equal_fact.line_file.clone(),
        });
        self.store_atomic_fact(&dim_equal)?;
        Ok(())
    }
}
