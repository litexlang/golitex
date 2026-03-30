use crate::prelude::*;
use std::collections::HashMap;

impl Runtime {
    /// Infer consequences from membership facts `x in S`.
    /// Example: `x in {1,2}` infers `x = 1 or x = 2`.
    pub(crate) fn infer_in_fact(&mut self, in_fact: &InFact) -> Result<InferResult, InferError> {
        match &in_fact.set {
            Obj::FnSetWithParams(fn_set_with_dom) => {
                let is_element_atom = match &in_fact.element {
                    Obj::Identifier(_)
                    | Obj::IdentifierWithMod(_)
                    | Obj::FieldAccess(_)
                    | Obj::FieldAccessWithMod(_) => true,
                    _ => false,
                };

                if !is_element_atom {
                    return Ok(InferResult::new());
                }

                let key = in_fact.element.to_string();
                let fn_set_obj = FnSetObj::FnSetWithDom(fn_set_with_dom.clone());
                let env = self.top_level_env();
                env.known_fn_in_fn_set.insert(key, fn_set_obj);
                Ok(InferResult::new())
            }
            Obj::FnSetWithoutParams(fn_set_without_dom) => {
                let is_element_atom = match &in_fact.element {
                    Obj::Identifier(_)
                    | Obj::IdentifierWithMod(_)
                    | Obj::FieldAccess(_)
                    | Obj::FieldAccessWithMod(_) => true,
                    _ => false,
                };

                if !is_element_atom {
                    return Ok(InferResult::new());
                }

                let key = in_fact.element.to_string();
                let fn_set_obj = FnSetObj::FnSetWithoutParams(fn_set_without_dom.clone());
                self.top_level_env()
                    .known_fn_in_fn_set
                    .insert(key, fn_set_obj);
                Ok(InferResult::new())
            }
            Obj::ListSet(list_set) => {
                if list_set.list.is_empty() {
                    return Ok(InferResult::new());
                }

                let mut or_case_facts: Vec<AndChainAtomicFact> =
                    Vec::with_capacity(list_set.list.len());
                for obj_in_list_set in list_set.list.iter() {
                    let equal_fact = AtomicFact::EqualFact(EqualFact::new(
                        in_fact.element.clone(),
                        *obj_in_list_set.clone(),
                        in_fact.line_file,
                    ));
                    or_case_facts.push(AndChainAtomicFact::AtomicFact(equal_fact));
                }

                let or_fact = Fact::OrFact(OrFact::new(or_case_facts, in_fact.line_file));
                self.store_fact_without_well_defined_verified_and_infer(&or_fact)
                    .map_err(|previous_error| {
                        InferError::new(
                            format!(
                                "failed to store inferred or fact while inferring `{}`",
                                in_fact
                            ),
                            in_fact.line_file,
                            Some(previous_error.into()),
                        )
                    })?;

                let mut infer_result = InferResult::new();
                infer_result.new_fact(&or_fact);
                Ok(infer_result)
            }
            Obj::SetBuilder(set_builder) => {
                let mut param_to_arg_map: HashMap<String, Obj> = HashMap::new();
                param_to_arg_map.insert(set_builder.param.clone(), in_fact.element.clone());

                let element_in_param_set_fact = Fact::AtomicFact(AtomicFact::InFact(InFact::new(
                    in_fact.element.clone(),
                    *set_builder.param_set.clone(),
                    in_fact.line_file,
                )));

                self.store_fact_without_well_defined_verified_and_infer(&element_in_param_set_fact)
                    .map_err(|previous_error| {
                        InferError::new(
                            format!(
                                "failed to store inferred in fact while inferring `{}`",
                                in_fact
                            ),
                            in_fact.line_file,
                            Some(previous_error.into()),
                        )
                    })?;

                let mut infer_result = InferResult::new();
                infer_result.new_fact(&element_in_param_set_fact);

                for fact_in_set_builder in set_builder.facts.iter() {
                    let instantiated_fact_in_set_builder: OrAndChainAtomicFact =
                        fact_in_set_builder.instantiate(&param_to_arg_map);
                    let instantiated_fact_as_fact = instantiated_fact_in_set_builder.to_fact();
                    let fact_to_store =
                        instantiated_fact_as_fact.with_new_line_file(in_fact.line_file);

                    self.store_fact_without_well_defined_verified_and_infer(&fact_to_store)
                        .map_err(|previous_error| {
                            InferError::new(
                                format!(
                                    "failed to store inferred set builder fact while inferring `{}`",
                                    in_fact
                                ),
                                in_fact.line_file,
                                Some(previous_error.into()),
                            )
                        })?;
                    infer_result.new_fact(&fact_to_store);
                }

                Ok(infer_result)
            }
            Obj::Cart(cart) => {
                let mut infer_result = InferResult::new();

                let is_cart_fact = Fact::AtomicFact(AtomicFact::IsTupleFact(IsTupleFact::new(
                    in_fact.element.clone(),
                    in_fact.line_file,
                )));

                self.store_fact_without_well_defined_verified_and_infer(&is_cart_fact)
                    .map_err(|previous_error| {
                        InferError::new(
                            format!(
                                "failed to store inferred is cart fact while inferring `{}`",
                                in_fact
                            ),
                            in_fact.line_file,
                            Some(previous_error.into()),
                        )
                    })?;
                infer_result.new_fact(&is_cart_fact);

                let cart_args_count = cart.args.len();
                let tuple_dim_obj = Obj::TupleDim(TupleDim::new(in_fact.element.clone()));
                let cart_args_count_obj = Obj::Number(Number::new(cart_args_count.to_string()));
                let tuple_dim_fact = Fact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(
                    tuple_dim_obj,
                    cart_args_count_obj,
                    in_fact.line_file,
                )));

                self.store_fact_without_well_defined_verified_and_infer(&tuple_dim_fact)
                    .map_err(|previous_error| {
                        InferError::new(
                            format!(
                                "failed to store inferred tuple_dim equals cart args count fact while inferring `{}`",
                                in_fact
                            ),
                            in_fact.line_file,
                            Some(previous_error.into()),
                        )
                    })?;
                infer_result.new_fact(&tuple_dim_fact);

                self.store_tuple_obj_and_cart(
                    &in_fact.element.to_string(),
                    None,
                    Some(cart.clone()),
                    in_fact.line_file,
                );

                Ok(infer_result)
            }
            Obj::Range(_) | Obj::ClosedRange(_) => {
                let inferred_in_z_fact = AtomicFact::InFact(InFact::new(
                    in_fact.element.clone(),
                    Obj::StandardSet {
                        standard_set: StandardSet::Z,
                    },
                    in_fact.line_file,
                ));
                self.store_atomic_fact_without_well_defined_verified_and_infer(&inferred_in_z_fact)
                    .map_err(|previous_error| {
                        InferError::new(
                            format!(
                                "failed to store inferred integer membership while inferring `{}`",
                                in_fact
                            ),
                            in_fact.line_file,
                            Some(previous_error.into()),
                        )
                    })?;

                let mut infer_result = InferResult::new();
                infer_result.push_atomic_fact(&inferred_in_z_fact);
                Ok(infer_result)
            }
            Obj::StandardSet {
                standard_set: StandardSet::QPos,
            }
            | Obj::StandardSet {
                standard_set: StandardSet::RPos,
            }
            | Obj::StandardSet {
                standard_set: StandardSet::NPos,
            } => {
                let zero_obj = Obj::Number(Number::new("0".to_string()));
                let inferred_atomic_fact = AtomicFact::GreaterFact(GreaterFact::new(
                    in_fact.element.clone(),
                    zero_obj,
                    in_fact.line_file,
                ));
                self.store_atomic_fact_without_well_defined_verified_and_infer(
                    &inferred_atomic_fact,
                )
                .map_err(|previous_error| {
                    InferError::new(
                        format!(
                            "failed to store inferred greater-than-zero while inferring `{}`",
                            in_fact
                        ),
                        in_fact.line_file,
                        Some(previous_error.into()),
                    )
                })?;
                let mut infer_result = InferResult::new();
                infer_result.push_atomic_fact(&inferred_atomic_fact);
                Ok(infer_result)
            }
            Obj::StandardSet {
                standard_set: StandardSet::QNeg,
            }
            | Obj::StandardSet {
                standard_set: StandardSet::ZNeg,
            }
            | Obj::StandardSet {
                standard_set: StandardSet::RNeg,
            } => {
                let zero_obj = Obj::Number(Number::new("0".to_string()));
                let inferred_atomic_fact = AtomicFact::LessFact(LessFact::new(
                    in_fact.element.clone(),
                    zero_obj,
                    in_fact.line_file,
                ));
                self.store_atomic_fact_without_well_defined_verified_and_infer(
                    &inferred_atomic_fact,
                )
                .map_err(|previous_error| {
                    InferError::new(
                        format!(
                            "failed to store inferred less-than-zero while inferring `{}`",
                            in_fact
                        ),
                        in_fact.line_file,
                        Some(previous_error.into()),
                    )
                })?;
                let mut infer_result = InferResult::new();
                infer_result.push_atomic_fact(&inferred_atomic_fact);
                Ok(infer_result)
            }
            Obj::StandardSet {
                standard_set: StandardSet::QNz,
            }
            | Obj::StandardSet {
                standard_set: StandardSet::ZNz,
            }
            | Obj::StandardSet {
                standard_set: StandardSet::RNz,
            } => {
                let zero_obj = Obj::Number(Number::new("0".to_string()));
                let inferred_atomic_fact = AtomicFact::NotEqualFact(NotEqualFact::new(
                    in_fact.element.clone(),
                    zero_obj,
                    in_fact.line_file,
                ));
                self.store_atomic_fact_without_well_defined_verified_and_infer(
                    &inferred_atomic_fact,
                )
                .map_err(|previous_error| {
                    InferError::new(
                        format!(
                            "failed to store inferred not-equal-to-zero while inferring `{}`",
                            in_fact
                        ),
                        in_fact.line_file,
                        Some(previous_error.into()),
                    )
                })?;
                let mut infer_result = InferResult::new();
                infer_result.push_atomic_fact(&inferred_atomic_fact);
                Ok(infer_result)
            }
            Obj::StandardSet {
                standard_set: StandardSet::N,
            }
            | Obj::StandardSet {
                standard_set: StandardSet::Q,
            }
            | Obj::StandardSet {
                standard_set: StandardSet::Z,
            }
            | Obj::StandardSet {
                standard_set: StandardSet::R,
            } => Ok(InferResult::new()),
            _ => Ok(InferResult::new()),
        }
    }
}
