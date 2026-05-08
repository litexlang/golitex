use crate::prelude::*;
use std::collections::{HashMap, HashSet};

impl Runtime {
    pub fn exec_by_struct_stmt(&mut self, stmt: &ByStructStmt) -> Result<StmtResult, RuntimeError> {
        let stmt_exec: Stmt = stmt.clone().into();
        let verify_state = VerifyState::new(0, false);

        let forall_as_fact: Fact = stmt.forall_fact.clone().into();
        let forall_verified = self
            .verify_fact(&forall_as_fact, &verify_state)
            .map_err(|e| {
                short_exec_error(
                    stmt_exec.clone(),
                    "by struct: failed to verify the forall fact".to_string(),
                    Some(e),
                    vec![],
                )
            })?;
        if forall_verified.is_unknown() {
            return Err(short_exec_error(
                stmt_exec,
                "by struct: the forall fact is not verified".to_string(),
                None,
                vec![],
            ));
        }

        self.verify_forall_fact_params_and_dom_well_defined(&stmt.forall_fact, &verify_state)
            .map_err(|e| {
                short_exec_error(
                    stmt_exec.clone(),
                    "by struct: forall parameters or domain are not well-defined".to_string(),
                    Some(e),
                    vec![],
                )
            })?;

        let mut arg_map: HashMap<String, Obj> = HashMap::new();
        let mut struct_binding_names: HashSet<String> = HashSet::new();
        for binding in stmt.struct_bindings.iter() {
            Self::insert_by_struct_arg(
                &mut arg_map,
                &binding.name,
                binding.tuple.clone(),
                stmt_exec.clone(),
            )?;
            struct_binding_names.insert(binding.name.clone());
        }
        for binding in stmt.value_bindings.iter() {
            Self::insert_by_struct_arg(
                &mut arg_map,
                &binding.name,
                binding.value.clone(),
                stmt_exec.clone(),
            )?;
        }

        let param_names = stmt.forall_fact.params_def_with_type.collect_param_names();
        for name in param_names.iter() {
            if !arg_map.contains_key(name) {
                return Err(short_exec_error(
                    stmt_exec.clone(),
                    format!(
                        "by struct: missing argument for forall parameter `{}`",
                        name
                    ),
                    None,
                    vec![],
                ));
            }
        }
        for name in arg_map.keys() {
            if !param_names.contains(name) {
                return Err(short_exec_error(
                    stmt_exec.clone(),
                    format!(
                        "by struct: `{}` is not a parameter of the forall fact",
                        name
                    ),
                    None,
                    vec![],
                ));
            }
        }

        let args_for_params = param_names
            .iter()
            .map(|name| arg_map.get(name).cloned().unwrap())
            .collect::<Vec<_>>();
        let instantiated_types = self
            .inst_param_def_with_type_one_by_one(
                &stmt.forall_fact.params_def_with_type,
                &args_for_params,
                ParamObjType::Forall,
            )
            .map_err(|e| {
                short_exec_error(
                    stmt_exec.clone(),
                    "by struct: failed to instantiate forall parameter types".to_string(),
                    Some(e),
                    vec![],
                )
            })?;
        let flat_types = stmt
            .forall_fact
            .params_def_with_type
            .flat_instantiated_types_for_args(&instantiated_types);

        for (name, param_type) in param_names.iter().zip(flat_types.iter()) {
            if struct_binding_names.contains(name) {
                let binding = stmt
                    .struct_bindings
                    .iter()
                    .find(|b| &b.name == name)
                    .unwrap();
                self.verify_by_struct_binding(stmt_exec.clone(), binding, param_type)?;
            } else {
                let value = arg_map.get(name).cloned().unwrap();
                let result = self
                    .verify_obj_satisfies_param_type(value, param_type, &verify_state)
                    .map_err(|e| {
                        short_exec_error(
                            stmt_exec.clone(),
                            format!(
                                "by struct: argument for `{}` does not satisfy its type",
                                name
                            ),
                            Some(e),
                            vec![],
                        )
                    })?;
                if result.is_unknown() {
                    return Err(short_exec_error(
                        stmt_exec.clone(),
                        format!(
                            "by struct: argument for `{}` does not satisfy its type",
                            name
                        ),
                        None,
                        vec![],
                    ));
                }
            }
        }

        for binding in stmt.struct_bindings.iter() {
            self.add_by_struct_field_args_to_map(stmt_exec.clone(), binding, &mut arg_map)?;
        }

        for dom_fact in stmt.forall_fact.dom_facts.iter() {
            let instantiated_dom = self
                .inst_fact(dom_fact, &arg_map, ParamObjType::Forall, None)
                .map_err(|e| {
                    short_exec_error(
                        stmt_exec.clone(),
                        "by struct: failed to instantiate forall domain fact".to_string(),
                        Some(e),
                        vec![],
                    )
                })?;
            let result = self
                .verify_fact(&instantiated_dom, &verify_state)
                .map_err(|e| {
                    short_exec_error(
                        stmt_exec.clone(),
                        format!(
                            "by struct: failed to verify instantiated domain fact `{}`",
                            instantiated_dom
                        ),
                        Some(e),
                        vec![],
                    )
                })?;
            if result.is_unknown() {
                return Err(short_exec_error(
                    stmt_exec.clone(),
                    format!(
                        "by struct: instantiated domain fact is not verified `{}`",
                        instantiated_dom
                    ),
                    None,
                    vec![],
                ));
            }
        }

        let mut infer_result = InferResult::new();
        for fact in stmt.forall_fact.then_facts.iter() {
            let instantiated_fact = self
                .inst_exist_or_and_chain_atomic_fact(fact, &arg_map, ParamObjType::Forall, None)
                .map_err(|e| {
                    short_exec_error(
                        stmt_exec.clone(),
                        "by struct: failed to instantiate forall then fact".to_string(),
                        Some(e),
                        vec![],
                    )
                })?;
            infer_result.new_fact(&instantiated_fact.clone().to_fact());
            infer_result.new_infer_result_inside(
                self.verify_exist_or_and_chain_atomic_fact_well_defined_and_store_and_infer(
                    &instantiated_fact,
                    &verify_state,
                )
                .map_err(|e| {
                    short_exec_error(
                        stmt_exec.clone(),
                        "by struct: failed to store instantiated forall then fact".to_string(),
                        Some(e),
                        vec![],
                    )
                })?,
            );
        }

        Ok((NonFactualStmtSuccess::new(stmt_exec, infer_result, vec![])).into())
    }

    fn insert_by_struct_arg(
        arg_map: &mut HashMap<String, Obj>,
        name: &str,
        value: Obj,
        stmt_exec: Stmt,
    ) -> Result<(), RuntimeError> {
        if arg_map.contains_key(name) {
            return Err(short_exec_error(
                stmt_exec,
                format!("by struct: duplicate argument for `{}`", name),
                None,
                vec![],
            ));
        }
        arg_map.insert(name.to_string(), value);
        Ok(())
    }

    fn verify_by_struct_binding(
        &mut self,
        stmt_exec: Stmt,
        binding: &ByStructBinding,
        param_type: &ParamType,
    ) -> Result<(), RuntimeError> {
        let struct_ty = match param_type {
            ParamType::Struct(struct_ty) => struct_ty,
            _ => {
                return Err(short_exec_error(
                    stmt_exec,
                    format!(
                        "by struct: forall parameter `{}` is not a struct parameter",
                        binding.name
                    ),
                    None,
                    vec![],
                ));
            }
        };

        if binding.struct_ty.struct_name() != struct_ty.struct_name()
            || binding.struct_ty.args.len() != struct_ty.args.len()
            || binding
                .struct_ty
                .args
                .iter()
                .zip(struct_ty.args.iter())
                .any(|(left, right)| left.to_string() != right.to_string())
        {
            return Err(short_exec_error(
                stmt_exec,
                format!(
                    "by struct: binding type `{}` does not match forall parameter type `{}`",
                    binding.struct_ty, struct_ty
                ),
                None,
                vec![],
            ));
        }

        self.verify_param_type_well_defined(
            &ParamType::Struct(struct_ty.clone()),
            &VerifyState::new(0, false),
        )
        .map_err(|e| {
            short_exec_error(
                stmt_exec.clone(),
                format!("by struct: struct type `{}` is not well-defined", struct_ty),
                Some(e),
                vec![],
            )
        })?;

        let tuple = self.tuple_for_by_struct(&binding.tuple, stmt_exec.clone())?;
        let def = self
            .get_struct_definition_by_name(&struct_ty.struct_name())
            .cloned()
            .ok_or_else(|| {
                short_exec_error(
                    stmt_exec.clone(),
                    format!(
                        "by struct: struct `{}` is not defined",
                        struct_ty.struct_name()
                    ),
                    None,
                    vec![],
                )
            })?;
        if tuple.args.len() != def.fields.len() {
            return Err(short_exec_error(
                stmt_exec,
                format!(
                    "by struct: tuple for `{}` has {} field(s), but `{}` expects {}",
                    binding.name,
                    tuple.args.len(),
                    struct_ty.struct_name(),
                    def.fields.len()
                ),
                None,
                vec![],
            ));
        }

        let param_to_arg_map = match &def.param_def_with_dom {
            Some((param_def, _)) => {
                param_def.param_defs_and_args_to_param_to_arg_map(struct_ty.args.as_slice())
            }
            None => HashMap::new(),
        };
        for ((field_name, field_type), component) in def.fields.iter().zip(tuple.args.iter()) {
            let instantiated_field_type = self
                .inst_obj(field_type, &param_to_arg_map, ParamObjType::DefHeader)
                .map_err(|e| {
                    short_exec_error(
                        stmt_exec.clone(),
                        format!(
                            "by struct: failed to instantiate field `{}` type",
                            field_name
                        ),
                        Some(e),
                        vec![],
                    )
                })?;
            let result = self
                .verify_obj_satisfies_param_type(
                    component.as_ref().clone(),
                    &ParamType::Obj(instantiated_field_type),
                    &VerifyState::new(0, false),
                )
                .map_err(|e| {
                    short_exec_error(
                        stmt_exec.clone(),
                        format!(
                            "by struct: tuple component for field `{}` does not satisfy its type",
                            field_name
                        ),
                        Some(e),
                        vec![],
                    )
                })?;
            if result.is_unknown() {
                return Err(short_exec_error(
                    stmt_exec.clone(),
                    format!(
                        "by struct: tuple component for field `{}` does not satisfy its type",
                        field_name
                    ),
                    None,
                    vec![],
                ));
            }
        }

        Ok(())
    }

    fn add_by_struct_field_args_to_map(
        &mut self,
        stmt_exec: Stmt,
        binding: &ByStructBinding,
        arg_map: &mut HashMap<String, Obj>,
    ) -> Result<(), RuntimeError> {
        let tuple = self.tuple_for_by_struct(&binding.tuple, stmt_exec.clone())?;
        let def = self
            .get_struct_definition_by_name(&binding.struct_ty.struct_name())
            .cloned()
            .ok_or_else(|| {
                short_exec_error(
                    stmt_exec.clone(),
                    format!(
                        "by struct: struct `{}` is not defined",
                        binding.struct_ty.struct_name()
                    ),
                    None,
                    vec![],
                )
            })?;
        for ((field_name, _), component) in def.fields.iter().zip(tuple.args.iter()) {
            let field_access = FieldAccess::new(binding.name.clone(), field_name.clone());
            arg_map.insert(field_access.to_string(), component.as_ref().clone());
        }
        Ok(())
    }

    fn tuple_for_by_struct(&self, obj: &Obj, stmt_exec: Stmt) -> Result<Tuple, RuntimeError> {
        match obj {
            Obj::Tuple(tuple) => Ok(tuple.clone()),
            _ => self
                .get_obj_equal_to_tuple(&obj.to_string())
                .ok_or_else(|| {
                    short_exec_error(
                        stmt_exec,
                        format!("by struct: `{}` is not known to denote a tuple", obj),
                        None,
                        vec![],
                    )
                }),
        }
    }
}

#[cfg(test)]
mod by_struct_tests {
    use crate::prelude::*;

    #[test]
    fn by_struct_instantiates_struct_and_normal_forall_params() {
        let source = r#"
struct Point:
    x R
    y R

forall P struct Point, t R:
    P.x + t $in R

by struct P from (1, 2) as Point, t = 3:
    forall P struct Point, t R:
        P.x + t $in R
"#;
        let mut rt = Runtime::new_with_builtin_code();
        let (_results, err) = run_source_code(source, &mut rt);
        assert!(err.is_none());
    }

    #[test]
    fn by_struct_rejects_wrong_tuple_field_count() {
        let source = r#"
struct Point:
    x R
    y R

forall P struct Point:
    P.x $in R

by struct P from (1, 2, 3) as Point:
    forall P struct Point:
        P.x $in R
"#;
        let mut rt = Runtime::new_with_builtin_code();
        let (_results, err) = run_source_code(source, &mut rt);
        assert!(err.is_some());
    }
}
