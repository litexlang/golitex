//! 实参与 [`ParamDefWithParamType`] 展开类型的**验证**（不写入环境）。
//!
//! 调用顺序（自顶向下）：
//! 1. [`Runtime::verify_args_satisfy_param_def_flat_types`] — 对 `param_defs` + `args` 展开后逐对验证；
//! 2. [`Runtime::verify_obj_satisfies_param_type`] — 单个 `obj` 是否满足 `param_type`；
//! 3. [`Runtime::verify_obj_satisfies_struct_param_type`] — `struct` 时按字段递归，内部再调 2；
//! 4. [`field_access_append_field`] — 仅 struct 字段路径用。

use crate::prelude::*;

fn field_access_append_field(obj: &Obj, field_name: &str) -> Option<FieldAccess> {
    match obj {
        Obj::Identifier(i) => Some(FieldAccess::new(i.name.clone(), vec![field_name.to_string()])),
        Obj::FieldAccess(fa) => {
            let mut fields = fa.fields.clone();
            fields.push(field_name.to_string());
            Some(FieldAccess::new(fa.name.clone(), fields))
        }
        _ => None,
    }
}

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

        let expected_count = ParamDefWithParamType::number_of_params(&def.params_def_with_type);
        if struct_ty.params.len() != expected_count {
            return Err(VerifyError::new(
                Fact::AtomicFact(AtomicFact::InFact(InFact::new(
                    obj.clone(),
                    Obj::Identifier(Identifier::new(String::from("_"))),
                    DEFAULT_LINE_FILE.clone(),
                ))),
                format!(
                    "struct `{}` expects {} type argument(s), got {}",
                    struct_name,
                    expected_count,
                    struct_ty.params.len()
                ),
                DEFAULT_LINE_FILE,
                None,
            ));
        }

        let param_to_arg_map = ParamDefWithParamType::param_defs_and_args_to_param_to_arg_map(
            &def.params_def_with_type,
            &struct_ty.params,
        );

        if def.fields.is_empty() {
            self.verify_obj_well_defined_and_store_cache(&obj, verify_state)
                .map_err(|e| {
                    VerifyError::new(
                        Fact::AtomicFact(AtomicFact::InFact(InFact::new(
                            obj.clone(),
                            Obj::Identifier(Identifier::new(String::from("_"))),
                            DEFAULT_LINE_FILE.clone(),
                        ))),
                        e.msg.clone(),
                        e.line_file,
                        Some(RuntimeError::WellDefinedError(e)),
                    )
                })?;
            return Ok(NonErrStmtExecResult::NonFactualStmtSuccess(
                NonFactualStmtSuccess::new(
                    Stmt::DoNothingStmt(DoNothingStmt::new(DEFAULT_LINE_FILE)),
                    InferResult::new(),
                    vec![],
                ),
            ));
        }

        let mut last_result: Option<NonErrStmtExecResult> = None;
        for (field_name, field_pt) in def.fields.iter() {
            let instantiated = self.inst_param_type(field_pt, &param_to_arg_map).map_err(
                |e| {
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
                },
            )?;
            let Some(fa) = field_access_append_field(&obj, field_name) else {
                return Err(VerifyError::new(
                    Fact::AtomicFact(AtomicFact::InFact(InFact::new(
                        obj.clone(),
                        Obj::Identifier(Identifier::new(String::from("_"))),
                        DEFAULT_LINE_FILE.clone(),
                    ))),
                    "struct param satisfaction: object root must be identifier or field access"
                        .to_string(),
                    DEFAULT_LINE_FILE,
                    None,
                ));
            };
            let field_obj = Obj::FieldAccess(fa);
            let r = self.verify_obj_satisfies_param_type(field_obj, &instantiated, verify_state)?;
            if r.is_unknown() {
                return Ok(r);
            }
            last_result = Some(r);
        }

        Ok(last_result.unwrap_or_else(|| {
            NonErrStmtExecResult::NonFactualStmtSuccess(NonFactualStmtSuccess::new(
                Stmt::DoNothingStmt(DoNothingStmt::new(DEFAULT_LINE_FILE)),
                InferResult::new(),
                vec![],
            ))
        }))
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
                        "argument does not satisfy parameter type (unknown): {}",
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
