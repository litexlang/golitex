use crate::prelude::*;
use std::collections::HashMap;

impl Runtime {
    /// 解析 family 定义并将 `equal_to` 实例化为具体 member set（`x ∈ family F(...)` 的右侧语义）。
    fn instantiate_family_member_set(
        &mut self,
        family_ty: &FamilyObj,
    ) -> Result<Obj, RuntimeError> {
        let family_name = family_ty.name.to_string();
        let def = match self.get_cloned_family_definition_by_name(&family_name) {
            Some(d) => d,
            None => {
                return Err(
                    RuntimeError::new_unknown_error_with_msg_position_optional_fact_previous_error(
                        format!("family `{}` is not defined", family_name),
                        default_line_file(),
                        None,
                        None,
                    )
                    .into(),
                );
            }
        };
        let expected_count = ParamGroupWithParamType::number_of_params(&def.params_def_with_type);
        if family_ty.params.len() != expected_count {
            return Err(
                RuntimeError::new_unknown_error_with_msg_position_optional_fact_previous_error(
                    format!(
                        "family `{}` expects {} type argument(s), got {}",
                        family_name,
                        expected_count,
                        family_ty.params.len()
                    ),
                    default_line_file(),
                    None,
                    None,
                )
                .into(),
            );
        }
        let param_to_arg_map = ParamGroupWithParamType::param_defs_and_args_to_param_to_arg_map(
            &def.params_def_with_type,
            &family_ty.params,
        );
        self.inst_obj(&def.equal_to, &param_to_arg_map)
    }

    /// 参数声明为 `ParamType::Obj(Obj::FamilyObj(...))` 时：存储 `name ∈` 实例化后的 member set，并走 infer。
    pub(crate) fn infer_membership_in_family_for_param_binding(
        &mut self,
        name: &str,
        family_ty: &FamilyObj,
    ) -> Result<InferResult, RuntimeError> {
        let member_set = self.instantiate_family_member_set(family_ty)?;
        let type_fact = Fact::AtomicFact(AtomicFact::InFact(InFact::new(
            Obj::Identifier(Identifier::new(name.to_string())),
            member_set,
            default_line_file(),
        )));
        self.store_fact_without_well_defined_verified_and_infer(type_fact)
            .map_err(RuntimeError::from)
    }

    /// [`InFact`] 右侧为 `FamilyObj` 时：先实例化为具体 member set，再对 `element ∈ member_set` 做 membership infer。
    pub(crate) fn infer_membership_in_family_from_in_fact(
        &mut self,
        in_fact: &InFact,
        family_obj: &FamilyObj,
    ) -> Result<InferResult, RuntimeError> {
        let member_set = self.instantiate_family_member_set(family_obj)?;
        let expanded = InFact::new(
            in_fact.element.clone(),
            member_set,
            in_fact.line_file.clone(),
        );
        self.infer_in_fact(&expanded)
    }

    /// [`InFact`] 右侧为函数空间时：登记 `known_objs_in_fn_sets`（与 satisfy/store 路径可共用此副作用）。
    pub(crate) fn infer_membership_in_fn_set_from_in_fact(
        &mut self,
        in_fact: &InFact,
        fn_set_with_dom: &FnSet,
    ) -> Result<InferResult, RuntimeError> {
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
        let env = self.top_level_env();
        env.known_objs_in_fn_sets
            .insert(key, fn_set_with_dom.clone());

        let mut infer_result = InferResult::new();
        infer_result.new_fact(&Fact::AtomicFact(AtomicFact::InFact(in_fact.clone())));
        Ok(infer_result)
    }

    /// [`InFact`] 右侧为内涵集时：推出 `element ∈ param_set` 及实例化后的约束事实。
    pub(crate) fn infer_membership_in_set_builder_from_in_fact(
        &mut self,
        in_fact: &InFact,
        set_builder: &SetBuilder,
    ) -> Result<InferResult, RuntimeError> {
        let mut param_to_arg_map: HashMap<String, Obj> = HashMap::new();
        param_to_arg_map.insert(set_builder.param.clone(), in_fact.element.clone());

        let element_in_param_set_fact = Fact::AtomicFact(AtomicFact::InFact(InFact::new(
            in_fact.element.clone(),
            *set_builder.param_set.clone(),
            in_fact.line_file.clone(),
        )));

        let mut infer_result = InferResult::new();
        infer_result.new_fact(&element_in_param_set_fact);
        self.store_fact_without_well_defined_verified_and_infer(element_in_param_set_fact)
            .map_err(|previous_error| {
                RuntimeError::new_infer_error_with_msg_position_previous_error(
                    format!(
                        "failed to store inferred in fact while inferring `{}`",
                        in_fact
                    ),
                    in_fact.line_file.clone(),
                    Some(previous_error.into()),
                )
            })?;

        for fact_in_set_builder in set_builder.facts.iter() {
            let instantiated_fact_in_set_builder: OrAndChainAtomicFact = self
                .inst_or_and_chain_atomic_fact(fact_in_set_builder, &param_to_arg_map)
                .map_err(|e| {
                    RuntimeError::new_infer_error_with_msg_position_previous_error(
                        format!(
                            "failed to instantiate set builder fact while inferring `{}`",
                            in_fact
                        ),
                        in_fact.line_file.clone(),
                        Some(e),
                    )
                })?;
            let instantiated_fact_as_fact = instantiated_fact_in_set_builder.to_fact();
            let fact_to_store =
                instantiated_fact_as_fact.with_new_line_file(in_fact.line_file.clone());

            infer_result.new_fact(&fact_to_store);
            self.store_fact_without_well_defined_verified_and_infer(fact_to_store)
                .map_err(|previous_error| {
                    RuntimeError::new_infer_error_with_msg_position_previous_error(
                        format!(
                            "failed to store inferred set builder fact while inferring `{}`",
                            in_fact
                        ),
                        in_fact.line_file.clone(),
                        Some(previous_error.into()),
                    )
                })?;
        }

        Ok(infer_result)
    }

    /// Infer consequences from membership facts `x in S`.
    /// Example: `x in {1,2}` infers `x = 1 or x = 2`.
    pub(in crate::infer) fn infer_in_fact(
        &mut self,
        in_fact: &InFact,
    ) -> Result<InferResult, RuntimeError> {
        match &in_fact.set {
            Obj::FnSet(fn_set_with_dom) => {
                self.infer_membership_in_fn_set_from_in_fact(in_fact, fn_set_with_dom)
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
                        in_fact.line_file.clone(),
                    ));
                    or_case_facts.push(AndChainAtomicFact::AtomicFact(equal_fact));
                }

                let or_fact = Fact::OrFact(OrFact::new(or_case_facts, in_fact.line_file.clone()));
                let mut infer_result = InferResult::new();
                infer_result.new_fact(&or_fact);
                self.store_fact_without_well_defined_verified_and_infer(or_fact)
                    .map_err(|previous_error| {
                        RuntimeError::new_infer_error_with_msg_position_previous_error(
                            format!(
                                "failed to store inferred or fact while inferring `{}`",
                                in_fact
                            ),
                            in_fact.line_file.clone(),
                            Some(previous_error.into()),
                        )
                    })?;
                Ok(infer_result)
            }
            Obj::SetBuilder(set_builder) => {
                self.infer_membership_in_set_builder_from_in_fact(in_fact, set_builder)
            }
            Obj::Cart(cart) => {
                let mut infer_result = InferResult::new();

                let is_cart_fact = Fact::AtomicFact(AtomicFact::IsTupleFact(IsTupleFact::new(
                    in_fact.element.clone(),
                    in_fact.line_file.clone(),
                )));

                infer_result.new_fact(&is_cart_fact);
                self.store_fact_without_well_defined_verified_and_infer(is_cart_fact)
                    .map_err(|previous_error| {
                        RuntimeError::new_infer_error_with_msg_position_previous_error(
                            format!(
                                "failed to store inferred is cart fact while inferring `{}`",
                                in_fact
                            ),
                            in_fact.line_file.clone(),
                            Some(previous_error.into()),
                        )
                    })?;

                let cart_args_count = cart.args.len();
                let tuple_dim_obj = Obj::TupleDim(TupleDim::new(in_fact.element.clone()));
                let cart_args_count_obj = Obj::Number(Number::new(cart_args_count.to_string()));
                let tuple_dim_fact = Fact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(
                    tuple_dim_obj,
                    cart_args_count_obj,
                    in_fact.line_file.clone(),
                )));

                infer_result.new_fact(&tuple_dim_fact);
                self.store_fact_without_well_defined_verified_and_infer(tuple_dim_fact)
                    .map_err(|previous_error| {
                        RuntimeError::new_infer_error_with_msg_position_previous_error(
                            format!(
                                "failed to store inferred tuple_dim equals cart args count fact while inferring `{}`",
                                in_fact
                            ),
                            in_fact.line_file.clone(),
                            Some(previous_error.into()),
                        )
                    })?;

                self.store_tuple_obj_and_cart(
                    &in_fact.element.to_string(),
                    None,
                    Some(cart.clone()),
                    in_fact.line_file.clone(),
                );

                Ok(infer_result)
            }
            Obj::Range(_) | Obj::ClosedRange(_) => {
                let inferred_in_z_fact = AtomicFact::InFact(InFact::new(
                    in_fact.element.clone(),
                    Obj::StandardSet(StandardSet::Z),
                    in_fact.line_file.clone(),
                ));
                let mut infer_result = InferResult::new();
                infer_result.push_atomic_fact(&inferred_in_z_fact);
                self.store_atomic_fact_without_well_defined_verified_and_infer(
                    inferred_in_z_fact.clone(),
                )
                .map_err(|previous_error| {
                    RuntimeError::new_infer_error_with_msg_position_previous_error(
                        format!(
                            "failed to store inferred integer membership while inferring `{}`",
                            in_fact
                        ),
                        in_fact.line_file.clone(),
                        Some(previous_error.into()),
                    )
                })?;
                Ok(infer_result)
            }
            Obj::StandardSet(StandardSet::QPos)
            | Obj::StandardSet(StandardSet::RPos)
            | Obj::StandardSet(StandardSet::NPos) => {
                let zero_obj = Obj::Number(Number::new("0".to_string()));
                let inferred_atomic_fact = AtomicFact::GreaterFact(GreaterFact::new(
                    in_fact.element.clone(),
                    zero_obj,
                    in_fact.line_file.clone(),
                ));
                let mut infer_result = InferResult::new();
                infer_result.push_atomic_fact(&inferred_atomic_fact);
                self.store_atomic_fact_without_well_defined_verified_and_infer(
                    inferred_atomic_fact.clone(),
                )
                .map_err(|previous_error| {
                    RuntimeError::new_infer_error_with_msg_position_previous_error(
                        format!(
                            "failed to store inferred greater-than-zero while inferring `{}`",
                            in_fact
                        ),
                        in_fact.line_file.clone(),
                        Some(previous_error.into()),
                    )
                })?;
                Ok(infer_result)
            }
            Obj::StandardSet(StandardSet::QNeg)
            | Obj::StandardSet(StandardSet::ZNeg)
            | Obj::StandardSet(StandardSet::RNeg) => {
                let zero_obj = Obj::Number(Number::new("0".to_string()));
                let inferred_atomic_fact = AtomicFact::LessFact(LessFact::new(
                    in_fact.element.clone(),
                    zero_obj,
                    in_fact.line_file.clone(),
                ));
                let mut infer_result = InferResult::new();
                infer_result.push_atomic_fact(&inferred_atomic_fact);
                self.store_atomic_fact_without_well_defined_verified_and_infer(
                    inferred_atomic_fact.clone(),
                )
                .map_err(|previous_error| {
                    RuntimeError::new_infer_error_with_msg_position_previous_error(
                        format!(
                            "failed to store inferred less-than-zero while inferring `{}`",
                            in_fact
                        ),
                        in_fact.line_file.clone(),
                        Some(previous_error.into()),
                    )
                })?;
                Ok(infer_result)
            }
            Obj::StandardSet(StandardSet::QNz)
            | Obj::StandardSet(StandardSet::ZNz)
            | Obj::StandardSet(StandardSet::RNz) => {
                let zero_obj = Obj::Number(Number::new("0".to_string()));
                let inferred_atomic_fact = AtomicFact::NotEqualFact(NotEqualFact::new(
                    in_fact.element.clone(),
                    zero_obj,
                    in_fact.line_file.clone(),
                ));
                let mut infer_result = InferResult::new();
                infer_result.push_atomic_fact(&inferred_atomic_fact);
                self.store_atomic_fact_without_well_defined_verified_and_infer(
                    inferred_atomic_fact.clone(),
                )
                .map_err(|previous_error| {
                    RuntimeError::new_infer_error_with_msg_position_previous_error(
                        format!(
                            "failed to store inferred not-equal-to-zero while inferring `{}`",
                            in_fact
                        ),
                        in_fact.line_file.clone(),
                        Some(previous_error.into()),
                    )
                })?;
                Ok(infer_result)
            }
            Obj::StandardSet(StandardSet::N)
            | Obj::StandardSet(StandardSet::Q)
            | Obj::StandardSet(StandardSet::Z)
            | Obj::StandardSet(StandardSet::R) => Ok(InferResult::new()),
            Obj::FamilyObj(family_obj) => {
                self.infer_membership_in_family_from_in_fact(in_fact, family_obj)
            }
            _ => Ok(InferResult::new()),
        }
    }
}
