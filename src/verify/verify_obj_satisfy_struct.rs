use crate::prelude::*;
use std::collections::HashMap;

impl Runtime {
    pub fn verify_obj_satisfies_struct_param_type(
        &mut self,
        obj: Obj,
        struct_ty: &StructObj,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let struct_name = struct_ty.name.to_string();
        let def = match self.get_cloned_definition_of_struct(&struct_name) {
            Some(d) => d,
            None => {
                return Err(
                    VerifyRuntimeError(RuntimeErrorStruct::new(
                None,
                format!("struct `{}` is not defined", struct_name),
                default_line_file(),
                None,
                vec![],
            ))
            .into(),
                );
            }
        };

        let number_of_params_in_def = def.number_of_params();
        if number_of_params_in_def != struct_ty.args.len() {
            return Err(VerifyRuntimeError(RuntimeErrorStruct::new(
                None,
                format!(
                    "struct `{}` definition expects {} parameter(s), but struct type has {} argument(s)",
                    def.name,
                    number_of_params_in_def,
                    struct_ty.args.len()
                ),
                default_line_file(),
                None,
                vec![],
            ))
            .into());
        }

        match &obj {
            Obj::Tuple(tuple) => self.run_in_local_env(|rt| {
                rt.verify_tuple_satisfy_struct(tuple, struct_ty, &def, verify_state)
            }),
            Obj::Identifier(_) | Obj::IdentifierWithMod(_) => {
                let id_key = match &obj {
                    Obj::Identifier(i) => IdentifierOrIdentifierWithMod::Identifier(i.clone()),
                    Obj::IdentifierWithMod(m) => {
                        IdentifierOrIdentifierWithMod::IdentifierWithMod(m.clone())
                    }
                    _ => {
                        return Ok((StmtUnknown::new()).into());
                    }
                };

                let Some(satisfied_struct) = self.get_object_satisfy_struct(&id_key).cloned()
                else {
                    return Ok((StmtUnknown::new()).into());
                };

                if satisfied_struct.name.to_string() != struct_ty.name.to_string() {
                    return Ok((StmtUnknown::new()).into());
                }

                if satisfied_struct.args.len() != struct_ty.args.len() {
                    return Ok((StmtUnknown::new()).into());
                }

                for (env_arg, given_arg) in satisfied_struct.args.iter().zip(struct_ty.args.iter())
                {
                    let result = self.verify_equal_fact(
                        &EqualFact::new(env_arg.clone(), given_arg.clone(), default_line_file()),
                        verify_state,
                    )?;
                    if !result.is_true() {
                        return Ok(result);
                    }
                }

                Ok(
                    (FactualStmtSuccess::new_with_verified_by_known_fact_source_recording_facts(
                        InFact::new(obj.clone(), String::from("_").into(), default_line_file())
                            .into(),
                        "".to_string(),
                        None,
                        Some(default_line_file()),
                        vec![],
                    ))
                    .into(),
                )
            }
            _ => Ok((StmtUnknown::new()).into()),
        }
    }

    fn verify_tuple_satisfy_struct(
        &mut self,
        tuple: &Tuple,
        struct_param_type: &StructObj,
        struct_def: &DefStructStmt,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let args_of_struct_param_type = &struct_param_type.args;
        let expected_tuple_len = args_of_struct_param_type.len() + struct_def.fields.len();
        if expected_tuple_len != tuple.args.len() {
            return Err(
                VerifyRuntimeError(RuntimeErrorStruct::new(
                None,
                format!(
                        "tuple for struct `{}` should have {} component(s), got {}",
                        struct_param_type.name,
                        expected_tuple_len,
                        tuple.args.len()
                    ),
                default_line_file(),
                None,
                vec![],
            ))
            .into(),
            );
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
                &EqualFact::new(
                    tuple_arg.clone(),
                    struct_type_arg.clone(),
                    default_line_file(),
                ),
                verify_state,
            )?;
            if result.is_unknown() {
                return Ok(result);
            }
        }

        let mut param_arg_map: HashMap<String, Obj> = HashMap::new();
        for (i, key) in struct_def.get_params().iter().enumerate() {
            param_arg_map.insert(
                key.clone(),
                tuple_args_for_struct_param_type_args[i].clone(),
            );
        }

        // 验证：tuple_args_for_struct_param_type_fields 满足 field 对应的 实例化的 struct_type
        // e.g. (R, 0, +, neg) 中 (0, +, neg) 满足 struct group(R): zero: R, add: fn(x, y R) R, inv: fn(x R) R 中: 0 满足 zero:R, + 满足 add: fn(x, y R) R, neg 满足 inv: fn(x R) R
        let mut last_result: Option<StmtResult> = None;
        for (i, ((_, field_type), tuple_field_arg)) in struct_def
            .fields
            .iter()
            .zip(tuple_args_for_struct_param_type_fields.iter())
            .enumerate()
        {
            let instantiated_field_type = self
                .inst_param_type(field_type, &param_arg_map)
                .map_err(|e| {
                    RuntimeError::from(VerifyRuntimeError(RuntimeErrorStruct::new(
                None,
                format!(
                            "failed to instantiate field type {} of struct `{}`",
                            i, struct_def.name
                        ),
                default_line_file(),
                Some(e),
                vec![],
            )))
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

        param_arg_map.insert(SELF.to_string(), tuple.clone().into());

        // TODO TODO: 让 self 对应这个 def ，否则 无法 instantiate
        self.register_param_as_struct_instance(SELF, struct_param_type.clone());

        for iff_fact in struct_def.facts.iter() {
            let instantiated = self
                .inst_or_and_chain_atomic_fact(iff_fact, &param_arg_map)
                .map_err(|e| {
                    RuntimeError::from(VerifyRuntimeError(RuntimeErrorStruct::new(
                None,
                format!(
                            "struct `{}`: failed to instantiate `<=>:` fact: {}",
                            struct_def.name, e
                        ),
                default_line_file(),
                Some(e),
                vec![],
            )))
                })?;

            let result = self.verify_or_and_chain_atomic_fact(&instantiated, verify_state)?;
            if result.is_unknown() {
                return Ok(result);
            }
            last_result = Some(result);
        }

        Ok(last_result.unwrap_or_else(|| {
            StmtResult::NonFactualStmtSuccess(NonFactualStmtSuccess::new(
                DoNothingStmt::new(default_line_file()).into(),
                InferResult::new(),
                vec![],
            ))
        }))
    }
}
