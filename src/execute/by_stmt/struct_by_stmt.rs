use crate::prelude::*;
use std::collections::HashMap;

impl Runtime {
    /// 将实例化后的字段 [`ParamType`] 转为可出现在 `cart(...)` 中的 [`Obj`]（与 `$in` 右端一致）。
    fn param_type_to_cart_dimension_obj(&self, pt: &ParamType) -> Result<Obj, RuntimeError> {
        match pt {
            ParamType::Obj(o) => match o {
                Obj::FamilyObj(family_ty) => {
                    let family_name = family_ty.name.to_string();
                    let def = self
                        .get_cloned_family_definition_by_name(&family_name)
                        .ok_or_else(|| {
                            RuntimeError::new_unknown_error_with_msg_position_optional_stmt_previous_error(
                                format!("family `{}` is not defined", family_name),
                                default_line_file(),
                                None,
                                None,
                            )
                        })?;
                    let map = def
                        .params_def_with_type
                        .param_defs_and_args_to_param_to_arg_map(family_ty.params.as_slice());
                    self.inst_obj(&def.equal_to, &map)
                }
                _ => Ok(o.clone()),
            },
            ParamType::Struct(_)
            | ParamType::Set(_)
            | ParamType::NonemptySet(_)
            | ParamType::FiniteSet(_) => Err(
                RuntimeError::new_unknown_error_with_msg_position_optional_stmt_previous_error(
                    "by struct: this field parameter kind cannot be used as a cart dimension yet"
                        .to_string(),
                    default_line_file(),
                    None,
                    None,
                ),
            ),
        }
    }

    /// `by struct: struct q(R)` — 生成
    /// 1) `struct q(R) = { x cart(...): inst(<=>:) }`；
    /// 2) `forall <fresh> struct q(R): ...`（成员在 cart 内且 `t[i] = t.field`）。
    pub fn exec_by_struct_stmt(
        &mut self,
        stmt: &ByStructStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let stmt_exec = stmt.clone().into();
        let struct_ty = match &stmt.struct_obj {
            Obj::StructObj(s) => s.clone(),
            _ => {
                return Err(RuntimeError::from(RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                        stmt_exec,
                        "by struct: expected `struct name(...)` object".to_string(),
                        None,
                        vec![],
                    )));
            }
        };

        let struct_name = struct_ty.name.to_string();
        let def = match self.get_cloned_definition_of_struct(&struct_name) {
            Some(d) => d,
            None => {
                return Err(RuntimeError::from(RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                        stmt_exec.clone(),
                        format!("by struct: struct `{}` is not defined", struct_name),
                        None,
                        vec![],
                    )));
            }
        };

        let expected_count = def.param_defs.number_of_params();
        if struct_ty.args.len() != expected_count {
            return Err(RuntimeError::from(RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                    stmt_exec,
                    format!(
                        "by struct: struct `{}` expects {} type argument(s), got {}",
                        struct_name,
                        expected_count,
                        struct_ty.args.len()
                    ),
                    None,
                    vec![],
                )));
        }

        let param_to_arg_map = def
            .param_defs
            .param_defs_and_args_to_param_to_arg_map(struct_ty.args.as_slice());

        let mut cart_dims: Vec<Obj> = Vec::with_capacity(def.fields.len());
        for (_, field_ty) in def.fields.iter() {
            let pt = self.inst_param_type(field_ty, &param_to_arg_map)?;
            cart_dims.push(self.param_type_to_cart_dimension_obj(&pt)?);
        }
        let cart_obj = Cart::new(cart_dims).into();

        let verify_state = VerifyState::new(0, false);
        self.verify_obj_well_defined_and_store_cache(&stmt.struct_obj, &verify_state)
            .map_err(|e| {
                RuntimeError::from(RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                    stmt_exec.clone(),
                    format!(
                        "by struct: struct type object `{}` is not well-defined",
                        stmt.struct_obj
                    ),
                    Some(e.into()),
                    vec![],
                ))
            })?;
        self.verify_obj_well_defined_and_store_cache(&cart_obj, &verify_state)
            .map_err(|e| {
                RuntimeError::from(RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                    stmt_exec.clone(),
                    format!("by struct: cart `{}` is not well-defined", cart_obj),
                    Some(e.into()),
                    vec![],
                ))
            })?;

        let random_names = self.generate_random_unused_names(2);
        let forall_param = random_names[0].clone();
        let set_builder_param = random_names[1].clone();

        let forall_param_obj: Obj = forall_param.clone().into();

        let mut then_facts: Vec<ExistOrAndChainAtomicFact> = Vec::new();
        then_facts.push(
            InFact::new(
                forall_param_obj.clone(),
                cart_obj.clone(),
                stmt.line_file.clone(),
            )
            .into(),
        );
        for (i, (field_name, _)) in def.fields.iter().enumerate() {
            let idx = i + 1;
            let lhs = ObjAtIndex::new(forall_param_obj.clone(),
                Number::new(idx.to_string()).into()).into();
            let rhs = FieldAccess::new(forall_param.clone(), field_name.clone()).into();
            then_facts.push(EqualFact::new(lhs, rhs, stmt.line_file.clone()).into());
        }

        let forall_fact = ForallFact::new(
            ParamDefWithType::new(vec![ParamGroupWithParamType::new(
                vec![forall_param],
                ParamType::Struct(struct_ty.clone()),
            )]),
            vec![],
            then_facts,
            stmt.line_file.clone(),
        )
        .into();

        // `<=>:` 里 `self.field` 在定义验证时按「tuple 模型」展开。set-builder 的域变量 `x` 在 cart 上，
        // 故令 `self` 为 `(R, x[1], x[2], …)`：与 `def.fields` + `number_of_params` 的 tuple 下标一致，
        // `inst_field_access` 会把 `self.b` 等变成 `x[1]` 而非非法的 `x.b`。
        let x_obj: Obj = set_builder_param.clone().into();
        let mut tuple_components: Vec<Obj> =
            Vec::with_capacity(def.number_of_params() + def.fields.len());
        for a in struct_ty.args.iter() {
            tuple_components.push(a.clone());
        }
        for i in 0..def.fields.len() {
            tuple_components.push(ObjAtIndex::new(x_obj.clone(),
                Number::new((i + 1).to_string()).into()).into());
        }
        let self_as_tuple = Tuple::new(tuple_components).into();

        let mut extended_for_sb: HashMap<String, Obj> = param_to_arg_map.clone();
        extended_for_sb.insert(SELF.to_string(), self_as_tuple);

        // `inst_field_access_on_struct_tuple` 用 `field_access.name`（此处为 `self`）查
        // `get_definition_of_struct_where_object_satisfies`；须登记 `self` 满足本 `struct q(R)`。
        self.register_param_as_struct_instance(SELF, struct_ty.clone());

        let mut inst_body_facts: Vec<OrAndChainAtomicFact> = Vec::with_capacity(def.facts.len());
        for fact in def.facts.iter() {
            inst_body_facts.push(self.inst_or_and_chain_atomic_fact(fact, &extended_for_sb)?);
        }

        let set_builder = SetBuilder::new_with_mangled_name(
            set_builder_param,
            cart_obj.clone(),
            inst_body_facts,
        );
        let rhs_sb_obj: Obj = set_builder.clone().into();
        self.verify_obj_well_defined_and_store_cache(&rhs_sb_obj, &verify_state)
            .map_err(|e| {
                RuntimeError::from(RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                    stmt_exec.clone(),
                    "by struct: set-builder (right-hand side) is not well-defined".to_string(),
                    Some(e.into()),
                    vec![],
                ))
            })?;

        let definitional_eq = EqualFact::new(
            Obj::StructObj(struct_ty.clone()),
            rhs_sb_obj,
            stmt.line_file.clone(),
        ).into();

        let mut infer_result = InferResult::new();
        infer_result.push_atomic_fact(&definitional_eq);
        infer_result.new_infer_result_inside(
            self.store_atomic_fact_without_well_defined_verified_and_infer(definitional_eq)
                .map_err(RuntimeError::from)?,
        );

        infer_result.new_fact(&forall_fact);
        infer_result.new_infer_result_inside(
            self.store_fact_without_well_defined_verified_and_infer(forall_fact)
                .map_err(RuntimeError::from)?,
        );

        Ok((NonFactualStmtSuccess::new(stmt_exec, infer_result, vec![])).into())
    }
}
