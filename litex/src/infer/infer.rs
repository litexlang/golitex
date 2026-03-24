use crate::error::InferError;
use crate::execute::Runtime;
use crate::fact::{
    AndChainAtomicFact, AndFact, AtomicFact, ChainFact, EqualFact, ExistFact,
    ExistOrAndChainAtomicFact, Fact, ForallFact, ForallFactWithIff, InFact, IsTupleFact,
    NormalAtomicFact, OrAndChainAtomicFact, OrFact,
};
use crate::obj::{FnSetObj, Number, Obj, TupleDimObj, ZObj};
use crate::stmt::parameter_def::ParamDefWithParamType;
use std::collections::HashMap;

#[derive(Clone, Debug)]
pub struct InferResult {
    pub infer_facts: Vec<String>,
}

impl InferResult {
    pub fn new() -> Self {
        InferResult {
            infer_facts: vec![],
        }
    }

    pub fn new_fact(&mut self, fact: &Fact) {
        self.infer_facts.push(fact.to_string());
    }

    pub fn push_atomic_fact(&mut self, atomic_fact: &AtomicFact) {
        self.infer_facts.push(atomic_fact.to_string());
    }

    pub fn new_infer_result_inside(&mut self, other_infer_result: InferResult) {
        for infer_fact in other_infer_result.infer_facts {
            self.infer_facts.push(infer_fact);
        }
    }
}

impl<'a> Runtime<'a> {
    pub fn infer(&mut self, fact: &Fact) -> Result<InferResult, InferError> {
        match fact {
            Fact::AtomicFact(atomic_fact) => self.infer_atomic_fact(atomic_fact),
            Fact::ExistFact(exist_fact) => self.infer_exist_fact(exist_fact),
            Fact::OrFact(or_fact) => self.infer_or_fact(or_fact),
            Fact::AndFact(and_fact) => self.infer_and_fact(and_fact),
            Fact::ChainFact(chain_fact) => self.infer_chain_fact(chain_fact),
            Fact::ForallFact(forall_fact) => self.infer_forall_fact(forall_fact),
            Fact::ForallFactWithIff(forall_fact_with_iff) => {
                self.infer_forall_fact_with_iff(forall_fact_with_iff)
            }
        }
    }

    pub fn infer_exist_or_and_chain_atomic_fact(
        &mut self,
        fact: &ExistOrAndChainAtomicFact,
    ) -> Result<InferResult, InferError> {
        match fact {
            ExistOrAndChainAtomicFact::AtomicFact(atomic_fact) => {
                self.infer_atomic_fact(atomic_fact)
            }
            ExistOrAndChainAtomicFact::AndFact(and_fact) => self.infer_and_fact(and_fact),
            ExistOrAndChainAtomicFact::ChainFact(chain_fact) => self.infer_chain_fact(chain_fact),
            ExistOrAndChainAtomicFact::OrFact(or_fact) => self.infer_or_fact(or_fact),
            ExistOrAndChainAtomicFact::ExistFact(exist_fact) => self.infer_exist_fact(exist_fact),
        }
    }

    pub fn infer_or_and_chain_atomic_fact(
        &mut self,
        fact: &OrAndChainAtomicFact,
    ) -> Result<InferResult, InferError> {
        match fact {
            OrAndChainAtomicFact::AtomicFact(atomic_fact) => self.infer_atomic_fact(atomic_fact),
            OrAndChainAtomicFact::AndFact(and_fact) => self.infer_and_fact(and_fact),
            OrAndChainAtomicFact::ChainFact(chain_fact) => self.infer_chain_fact(chain_fact),
            OrAndChainAtomicFact::OrFact(or_fact) => self.infer_or_fact(or_fact),
        }
    }

    fn infer_atomic_fact(&mut self, _atomic_fact: &AtomicFact) -> Result<InferResult, InferError> {
        match _atomic_fact {
            AtomicFact::EqualFact(equal_fact) => self.infer_equal_fact(equal_fact),
            AtomicFact::InFact(in_fact) => self.infer_in_fact(in_fact),
            AtomicFact::NormalAtomicFact(normal_atomic_fact) => {
                self.infer_normal_atomic_fact(normal_atomic_fact)
            }
            _ => Ok(InferResult::new()),
        }
    }

    fn infer_exist_fact(&mut self, _exist_fact: &ExistFact) -> Result<InferResult, InferError> {
        Ok(InferResult::new())
    }

    fn infer_or_fact(&mut self, _or_fact: &OrFact) -> Result<InferResult, InferError> {
        Ok(InferResult::new())
    }

    fn infer_and_fact(&mut self, _and_fact: &AndFact) -> Result<InferResult, InferError> {
        Ok(InferResult::new())
    }

    fn infer_chain_fact(&mut self, _chain_fact: &ChainFact) -> Result<InferResult, InferError> {
        Ok(InferResult::new())
    }

    fn infer_forall_fact(&mut self, _forall_fact: &ForallFact) -> Result<InferResult, InferError> {
        Ok(InferResult::new())
    }

    fn infer_forall_fact_with_iff(
        &mut self,
        _forall_fact_with_iff: &ForallFactWithIff,
    ) -> Result<InferResult, InferError> {
        Ok(InferResult::new())
    }

    fn infer_equal_fact(&mut self, _equal_fact: &EqualFact) -> Result<InferResult, InferError> {
        Ok(InferResult::new())
    }

    fn infer_in_fact(&mut self, in_fact: &InFact) -> Result<InferResult, InferError> {
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

                let env = self.runtime_context.top_level_env();
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
                let fn_set_obj = FnSetObj::FnSetWithoutDom(fn_set_without_dom.clone());

                self.runtime_context
                    .top_level_env()
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

                    self
                        .store_fact_without_well_defined_verified_and_infer(&fact_to_store)
                        .map_err(|previous_error| {
                            InferError::new(
                                format!("failed to store inferred set builder fact while inferring `{}`", in_fact),
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

                // tuple_dim(tuple) should equal the number of parameters of the `cart` set.
                let cart_args_count = cart.args.len();
                let tuple_dim_obj = Obj::TupleDimObj(TupleDimObj::new(in_fact.element.clone()));
                let cart_args_count_obj = Obj::Number(Number::new(cart_args_count.to_string()));

                let tuple_dim_fact = Fact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(
                    tuple_dim_obj,
                    cart_args_count_obj,
                    in_fact.line_file,
                )));

                self.store_fact_without_well_defined_verified_and_infer(&tuple_dim_fact).map_err(|previous_error| {
                    InferError::new(
                        format!("failed to store inferred tuple_dim equals cart args count fact while inferring `{}`", in_fact),
                        in_fact.line_file,
                        Some(previous_error.into()),
                    )
                })?;
                infer_result.new_fact(&tuple_dim_fact);

                self.runtime_context
                    .top_level_env()
                    .known_tuple_obj_in_what_cart
                    .insert(in_fact.element.to_string(), cart.clone());

                Ok(infer_result)
            }
            Obj::Range(_) | Obj::ClosedRange(_) => {
                let inferred_in_z_fact = AtomicFact::InFact(InFact::new(
                    in_fact.element.clone(),
                    Obj::ZObj(ZObj::new()),
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
            _ => Ok(InferResult::new()),
        }
    }

    fn infer_normal_atomic_fact(
        &mut self,
        normal_atomic_fact: &NormalAtomicFact,
    ) -> Result<InferResult, InferError> {
        let predicate_name = normal_atomic_fact.predicate.to_string();
        let predicate_definition = match self
            .runtime_context
            .get_predicate_with_meaning_definition_by_name(&predicate_name)
        {
            Some(predicate_definition) => predicate_definition.clone(),
            None => return Ok(InferResult::new()), // prop might be without meaning
        };
        let mut infer_result = InferResult::new();

        let param_type_facts =
            ParamDefWithParamType::facts_for_args_satisfy_param_def_with_type_vec(
                &predicate_definition.params_def_with_type,
                &normal_atomic_fact.body,
            )
            .map_err(|previous_error| {
                InferError::new(
                    format!(
                        "failed to infer parameter type facts for `{}`",
                        normal_atomic_fact
                    ),
                    normal_atomic_fact.line_file,
                    Some(previous_error),
                )
            })?;

        for param_type_fact in param_type_facts.iter() {
            let fact_to_store = param_type_fact
                .clone()
                .with_new_line_file(normal_atomic_fact.line_file);
            self.store_atomic_fact_without_well_defined_verified_and_infer(&fact_to_store)
                .map_err(|previous_error| {
                    InferError::new(
                        format!(
                            "failed to store parameter type fact while inferring `{}`",
                            normal_atomic_fact
                        ),
                        normal_atomic_fact.line_file,
                        Some(previous_error.into()),
                    )
                })?;
            infer_result.push_atomic_fact(&fact_to_store);
        }

        let param_to_arg_map = ParamDefWithParamType::param_defs_and_args_to_param_to_arg_map(
            &predicate_definition.params_def_with_type,
            &normal_atomic_fact.body,
        );

        for iff_fact in predicate_definition.iff_facts.iter() {
            let instantiated_iff_fact = iff_fact.instantiate(&param_to_arg_map);
            let fact_to_store =
                instantiated_iff_fact.with_new_line_file(normal_atomic_fact.line_file);

            self.store_fact_without_well_defined_verified_and_infer(&fact_to_store)
                .map_err(|previous_error| {
                    InferError::new(
                        format!(
                            "failed to store instantiated iff fact while inferring `{}`",
                            normal_atomic_fact
                        ),
                        normal_atomic_fact.line_file,
                        Some(previous_error.into()),
                    )
                })?;
            infer_result.new_fact(&fact_to_store);
        }

        Ok(infer_result)
    }
}
