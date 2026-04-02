use std::collections::HashMap;
use crate::prelude::*;

impl Runtime {
    fn verify_obj_satisfies_struct_param_type(
        &mut self,
        obj: Obj,
        struct_ty: &StructParamType,
        verify_state: &VerifyState,
    ) -> Result<NonErrStmtExecResult, VerifyError> {
        let struct_name = struct_ty.name.to_string();
        let def = match self.get_cloned_param_type_struct_definition_by_name(&struct_name) {
            Some(d) => d,
            None => {
                return Err(VerifyError::new(
                    Fact::AtomicFact(AtomicFact::InFact(InFact::new(
                        obj.clone(),
                        Obj::Identifier(Identifier::new(String::from("_"))),
                        DEFAULT_LINE_FILE.clone(),
                    ))),
                    format!("struct `{}` is not defined", struct_name),
                    DEFAULT_LINE_FILE,
                    None,
                ));
            }
        };

        let number_of_params_in_def = def.number_of_params();
        if number_of_params_in_def != struct_ty.args.len() {
            return Err(VerifyError::new(
                Fact::AtomicFact(AtomicFact::InFact(InFact::new(
                    obj.clone(),
                    Obj::Identifier(Identifier::new(String::from("_"))),
                    DEFAULT_LINE_FILE.clone(),
                ))),
                format!(
                    "struct `{}` definition expects {} parameter(s), but struct type has {} argument(s)",
                    def.name,
                    number_of_params_in_def,
                    struct_ty.args.len()
                ),
                DEFAULT_LINE_FILE,
                None,
            ));
        }
        
        match &obj {
            Obj::Tuple(tuple) => {
                self.verify_tuple_satisfy_param_def_with_struct_type(
                    tuple,
                    struct_ty,
                    &def,
                    verify_state,
                )
            }
            Obj::Identifier(_) | Obj::IdentifierWithMod(_) => {
                let expected_inst =
                    InstStructObj::new(struct_ty.name.clone(), struct_ty.args.clone());
                if let Some(inst) =
                    self.get_inst_struct_obj_for_field_access_root(&obj.to_string())
                {
                    if inst.to_string() == expected_inst.to_string() {
                        return Ok(NonErrStmtExecResult::NonFactualStmtSuccess(
                            NonFactualStmtSuccess::new(
                                Stmt::DoNothingStmt(DoNothingStmt::new(DEFAULT_LINE_FILE)),
                                InferResult::new(),
                                vec![],
                            ),
                        ));
                    }
                }
                Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()))
            }
            _ => Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new())),
        }
    }

    /// 检查 `obj` 是否满足 `param_type`（按 [`ParamType`] 各变体分别处理）。
    pub fn verify_obj_satisfies_param_type(
        &mut self,
        obj: Obj,
        param_type: &ParamType,
        verify_state: &VerifyState,
    ) -> Result<NonErrStmtExecResult, VerifyError> {
        match param_type {
            ParamType::Struct(struct_ty) => {
                self.verify_obj_satisfies_struct_param_type(obj, struct_ty, verify_state)
            }
            ParamType::Family(family_ty) => {
                let family_name = family_ty.name.to_string();
                let def = match self.get_cloned_family_definition_by_name(&family_name) {
                    Some(d) => d,
                    None => {
                        return Err(VerifyError::new(
                            Fact::AtomicFact(AtomicFact::InFact(InFact::new(
                                obj.clone(),
                                Obj::Identifier(Identifier::new(String::from("_"))),
                                DEFAULT_LINE_FILE.clone(),
                            ))),
                            format!("family `{}` is not defined", family_name),
                            DEFAULT_LINE_FILE,
                            None,
                        ));
                    }
                };
                let expected_count =
                    ParamDefWithParamType::number_of_params(&def.params_def_with_type);
                if family_ty.params.len() != expected_count {
                    return Err(VerifyError::new(
                        Fact::AtomicFact(AtomicFact::InFact(InFact::new(
                            obj.clone(),
                            Obj::Identifier(Identifier::new(String::from("_"))),
                            DEFAULT_LINE_FILE.clone(),
                        ))),
                        format!(
                            "family `{}` expects {} type argument(s), got {}",
                            family_name,
                            expected_count,
                            family_ty.params.len()
                        ),
                        DEFAULT_LINE_FILE,
                        None,
                    ));
                }
                let param_to_arg_map = ParamDefWithParamType::param_defs_and_args_to_param_to_arg_map(
                    &def.params_def_with_type,
                    &family_ty.params,
                );
                let member_set = self.inst_obj(&def.equal_to, &param_to_arg_map).map_err(|e| {
                    VerifyError::new(
                        Fact::AtomicFact(AtomicFact::InFact(InFact::new(
                            obj.clone(),
                            Obj::Identifier(Identifier::new(String::from("_"))),
                            DEFAULT_LINE_FILE.clone(),
                        ))),
                        String::new(),
                        DEFAULT_LINE_FILE,
                        Some(e),
                    )
                })?;
                let fact = AtomicFact::InFact(InFact::new(
                    obj,
                    member_set,
                    DEFAULT_LINE_FILE.clone(),
                ));
                self.verify_atomic_fact(&fact, verify_state)
            }
            ParamType::Obj(set_obj) => {
                let fact = AtomicFact::InFact(InFact::new(
                    obj,
                    set_obj.clone(),
                    DEFAULT_LINE_FILE.clone(),
                ));
                self.verify_atomic_fact(&fact, verify_state)
            }
            ParamType::Set(_) => {
                let fact = AtomicFact::IsSetFact(IsSetFact::new(obj, DEFAULT_LINE_FILE.clone()));
                self.verify_atomic_fact(&fact, verify_state)
            }
            ParamType::NonemptySet(_) => {
                let fact = AtomicFact::IsNonemptySetFact(IsNonemptySetFact::new(
                    obj,
                    DEFAULT_LINE_FILE.clone(),
                ));
                self.verify_atomic_fact(&fact, verify_state)
            }
            ParamType::FiniteSet(_) => {
                let fact =
                    AtomicFact::IsFiniteSetFact(IsFiniteSetFact::new(obj, DEFAULT_LINE_FILE.clone()));
                self.verify_atomic_fact(&fact, verify_state)
            }
        }
    }

    /// 对每个实参调用 [`Self::verify_obj_satisfies_param_type`]（含 `family` / `struct`），并合并各步的 [`InferResult`]。
    pub(crate) fn verify_args_satisfy_param_def_flat_types(
        &mut self,
        param_defs: &Vec<ParamDefWithParamType>,
        args: &Vec<Obj>,
        verify_state: &VerifyState,
    ) -> Result<InferResult, RuntimeError> {
        let instantiated_types =
            self.inst_param_def_with_type_one_by_one(param_defs, args)?;
        let flat_types = ParamDefWithParamType::flat_instantiated_types_for_args(
            param_defs,
            &instantiated_types,
        );
        let mut infer_result = InferResult::new();
        for (arg, param_type) in args.iter().zip(flat_types.iter()) {
            let verify_result = self
                .verify_obj_satisfies_param_type(arg.clone(), param_type, verify_state)
                .map_err(RuntimeError::from)?;
            if verify_result.is_unknown() {
                return Err(RuntimeError::UnknownError(UnknownError::new(
                    format!(
                        "argument {} does not satisfy parameter type (unknown): {}",
                        arg,
                        param_type
                    ),
                    DEFAULT_LINE_FILE.clone(),
                    None,
                    None,
                )));
            }
            match verify_result {
                NonErrStmtExecResult::NonFactualStmtSuccess(x) => {
                    infer_result.new_infer_result_inside(x.infers);
                }
                NonErrStmtExecResult::FactualStmtSuccess(x) => {
                    infer_result.new_infer_result_inside(x.infers);
                }
                NonErrStmtExecResult::StmtUnknown(_) => unreachable!(),
            }
        }
        Ok(infer_result)
    }
}

impl Runtime {
    fn verify_tuple_satisfy_param_def_with_struct_type(
        &mut self,
        tuple: &Tuple,
        struct_param_type: &StructParamType,
        struct_def: &DefParamTypeStructStmt,
        verify_state: &VerifyState,
    ) -> Result<NonErrStmtExecResult, VerifyError> {
        // 输入 (R, id, +, neg) 对应 struct group(s set): id: s, add: fn(x, y s)s, inv: fn(x s)s

        let args_of_struct_param_type = &struct_param_type.args;
        let expected_tuple_len = args_of_struct_param_type.len() + struct_def.fields.len();
        if expected_tuple_len != tuple.args.len() {
            return Err(VerifyError::new(
                Fact::AtomicFact(AtomicFact::InFact(InFact::new(
                    Obj::Tuple(tuple.clone()),
                    Obj::Identifier(Identifier::new(String::from("_"))),
                    DEFAULT_LINE_FILE.clone(),
                ))),
                format!(
                    "tuple for struct `{}` should have {} component(s), got {}",
                    struct_param_type.name,
                    expected_tuple_len,
                    tuple.args.len()
                ),
                DEFAULT_LINE_FILE,
                None,
            ));
        }

        let mut tuple_args_for_struct_param_type_args: Vec<Obj> = vec![];
        for i in 0..args_of_struct_param_type.len() {
            tuple_args_for_struct_param_type_args.push((*tuple.args[i]).clone());
        }

        let mut tuple_args_for_struct_param_type_fields: Vec<Obj> = vec![];
        for i in args_of_struct_param_type.len()
            ..args_of_struct_param_type.len() + struct_def.fields.len()
        {
            tuple_args_for_struct_param_type_fields.push((*tuple.args[i]).clone())
        }

        // tuple_args_for_struct_param_type_args 和 args_of_struct_param_type 一一对应相等
        for (i, tuple_arg) in tuple_args_for_struct_param_type_args.iter().enumerate() {
            let struct_type_arg = struct_param_type.args[i].clone();
            let result = self.verify_equal_fact(
                &EqualFact::new(tuple_arg.clone(), struct_type_arg.clone(), DEFAULT_LINE_FILE),
                verify_state,
            )?;
            if result.is_unknown() {
                return Err(VerifyError::new(
                    Fact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(
                        tuple_arg.clone(),
                        struct_type_arg.clone(),
                        DEFAULT_LINE_FILE.clone(),
                    ))),
                    format!(
                        "cannot verify tuple component {} equals struct type argument `{}`",
                        i, struct_type_arg
                    ),
                    DEFAULT_LINE_FILE,
                    None,
                ));
            }
        }

        let mut param_arg_map: HashMap<String, Obj> = HashMap::new();
        for (i, key) in struct_def.get_params().iter().enumerate() {
            param_arg_map.insert(key.clone(), tuple_args_for_struct_param_type_args[i].clone());
        }

        // 验证：tuple_args_for_struct_param_type_fields 满足 field 对应的 实例化的 struct_type 
        // e.g. (R, 0, +, neg) 中 (0, +, neg) 满足 struct group(R): zero: R, add: fn(x, y R) R, inv: fn(x R) R 中: 0 满足 zero:R, + 满足 add: fn(x, y R) R, neg 满足 inv: fn(x R) R
        let mut last_result: Option<NonErrStmtExecResult> = None;
        for (i, ((_, field_type), tuple_field_arg)) in struct_def
            .fields
            .iter()
            .zip(tuple_args_for_struct_param_type_fields.iter())
            .enumerate()
        {
            let instantiated_field_type = self
                .inst_param_type(&field_type.to_param_type(), &param_arg_map)
                .map_err(|e| {
                    VerifyError::new(
                        Fact::AtomicFact(AtomicFact::InFact(InFact::new(
                            tuple_field_arg.clone(),
                            Obj::Identifier(Identifier::new(String::from("_"))),
                            DEFAULT_LINE_FILE.clone(),
                        ))),
                        format!(
                            "failed to instantiate field type {} of struct `{}`",
                            i, struct_def.name
                        ),
                        DEFAULT_LINE_FILE,
                        Some(e),
                    )
                })?;
            let result = self.verify_obj_satisfies_param_type(
                tuple_field_arg.clone(),
                &instantiated_field_type,
                verify_state,
            )?;
            if result.is_unknown() {
                return Ok(result);
            }
            last_result = Some(result);
        }

        param_arg_map.insert(SELF.to_string(), Obj::Tuple(tuple.clone()));

        // TODO TODO: 让 self 对应这个 def ，否则 无法 instantiate
        
        for iff_fact in struct_def.facts.iter() {
            let instantiated = self
                .inst_or_and_chain_atomic_fact(iff_fact, &param_arg_map)
                .map_err(|e| {
                    VerifyError::new(
                        Fact::AtomicFact(AtomicFact::InFact(InFact::new(
                            Obj::Tuple(tuple.clone()),
                            Obj::Identifier(Identifier::new(String::from("_"))),
                            DEFAULT_LINE_FILE.clone(),
                        ))),
                        format!(
                            "struct `{}`: failed to instantiate `<=>:` fact: {}",
                            struct_def.name, e
                        ),
                        DEFAULT_LINE_FILE,
                        Some(e),
                    )
                })?;
            println!("instantiated: {:?}", instantiated.to_string());
            let result = self.verify_or_and_chain_atomic_fact(&instantiated, verify_state)?;
            if result.is_unknown() {
                return Ok(result);
            }
            last_result = Some(result);
        }

        Ok(last_result.unwrap_or_else(|| {
            NonErrStmtExecResult::NonFactualStmtSuccess(NonFactualStmtSuccess::new(
                Stmt::DoNothingStmt(DoNothingStmt::new(DEFAULT_LINE_FILE)),
                InferResult::new(),
                vec![],
            ))
        }))
    }
}