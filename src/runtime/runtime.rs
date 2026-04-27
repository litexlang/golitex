use crate::prelude::*;
use std::collections::HashMap;
use std::rc::Rc;

pub struct Runtime {
    pub module_manager: ModuleManager,
    pub environment_stack: Vec<Box<Environment>>,
    pub parsing_free_param_collection: FreeParamCollection,
}

impl Runtime {
    pub fn new() -> Self {
        let module_manager = ModuleManager::new_empty_module_manager(BUILTIN_CODE_PATH);
        let new_environment = Box::new(Environment::new_empty_env());

        Runtime {
            module_manager,
            environment_stack: vec![new_environment],
            parsing_free_param_collection: FreeParamCollection::new(),
        }
    }

    // Same empty runtime as `new`, then runs builtin definitions; panics if that fails.
    pub fn new_with_builtin_code() -> Self {
        let mut runtime = Self::new();
        let (stmt_results, runtime_error) =
            crate::pipeline::run_source_code(builtin_code().as_str(), &mut runtime);
        let (ok, msg) = crate::pipeline::render_run_source_code_output(
            &runtime,
            &stmt_results,
            &runtime_error,
            true,
        );
        if !ok {
            panic!("builtin code execution failed: {}", msg);
        }
        runtime
    }
}

impl Runtime {
    pub fn validate_name(
        &mut self,
        name: &str,
        _current_line_file: LineFile,
    ) -> Result<(), RuntimeError> {
        if let Err(invalid_name_message) = is_valid_litex_name(name) {
            return Err(ParseRuntimeError(RuntimeErrorStruct::new(
                None,
                invalid_name_message,
                default_line_file(),
                None,
                vec![],
            ))
            .into());
        }

        Ok(())
    }

    pub fn validate_user_fn_param_names_for_parse(
        &mut self,
        names: &[String],
        line_file: LineFile,
    ) -> Result<(), RuntimeError> {
        for name in names {
            if let Err(e) = is_valid_litex_name(name) {
                return Err(ParseRuntimeError(RuntimeErrorStruct::new(
                    None,
                    e,
                    line_file.clone(),
                    None,
                    vec![],
                ))
                .into());
            }
        }
        Ok(())
    }

    pub fn validate_names_and_insert_into_top_parsing_time_name_scope(
        &mut self,
        names: &Vec<String>,
        line_file: LineFile,
    ) -> Result<(), RuntimeError> {
        for name in names {
            self.validate_name_and_insert_into_top_parsing_time_name_scope(
                name,
                line_file.clone(),
            )?;
        }
        Ok(())
    }

    /// Validates identifier syntax only; does not record bindings (see `run_in_local_parsing_time_name_scope`).
    pub fn validate_name_and_insert_into_top_parsing_time_name_scope(
        &mut self,
        name: &str,
        line_file: LineFile,
    ) -> Result<(), RuntimeError> {
        self.validate_name(name, line_file)
    }
}

impl Runtime {
    pub fn new_file_path_new_env_new_name_scope(&mut self, path: &str) {
        let path_rc: Rc<str> = Rc::from(path);
        self.module_manager.run_file_paths.push(path_rc.clone());
        self.module_manager.current_file_index += 1;
        self.module_manager.display_entry_rc = Some(path_rc);
        self.module_manager.entry_path = path.to_string();
        self.push_env();
    }

    /// After `new_file_path_new_env_new_name_scope`, point the current user entry slot at another
    /// path without pushing more layers (pair with `clear_current_env_and_parse_name_scope`).
    pub fn set_current_user_lit_file_path(&mut self, path: &str) {
        let path_rc: Rc<str> = Rc::from(path);
        let idx = self.module_manager.current_file_index;
        debug_assert!(
            idx > FILE_INDEX_FOR_BUILTIN,
            "set_current_user_lit_file_path requires a prior new_file_path_new_env_new_name_scope"
        );
        if let Some(slot) = self.module_manager.run_file_paths.get_mut(idx) {
            *slot = path_rc.clone();
        }
        self.module_manager.display_entry_rc = Some(path_rc);
        self.module_manager.entry_path = path.to_string();
    }
}

impl Runtime {
    pub fn top_level_env(&mut self) -> &mut Environment {
        let result = self.environment_stack.last_mut();
        match result {
            Some(environment) => environment,
            None => unreachable!("no top level environment"),
        }
    }
}

impl Runtime {
    fn push_env(&mut self) {
        let new_env = Box::new(Environment::new_empty_env());
        self.environment_stack.push(new_env);
    }

    fn pop_env(&mut self) {
        let last_env = self.environment_stack.last();

        match last_env {
            None => {
                unreachable!("no top level environment")
            }
            Some(_) => {
                self.environment_stack.pop();
            }
        }
    }

    /// Replace the top environment with an empty one and clear parse-time free-param scopes.
    /// If there is only one environment layer (builtin), does nothing so builtins stay intact.
    pub fn clear_current_env_and_parse_name_scope(&mut self) {
        if self.environment_stack.len() > 1 {
            if let Some(top) = self.environment_stack.last_mut() {
                *top = Box::new(Environment::new_empty_env());
            }
        }
        self.parsing_free_param_collection.clear();
    }

    /// 在临时子环境中执行闭包：`push_env` → `f` → `pop_env`；`Ok`/`Err` 都会弹出。
    /// 与手写 `push`/`pop` 等价；若闭包 panic，栈不会恢复（与手写相同）。
    pub fn run_in_local_env<T, E, F>(&mut self, f: F) -> Result<T, E>
    where
        F: FnOnce(&mut Self) -> Result<T, E>,
    {
        self.push_env();
        let result = f(self);
        self.pop_env();
        result
    }

    /// Restores [`Runtime::parsing_free_param_collection`] after `f` so parse-time bindings (e.g.
    /// `have x …` without `=`) do not leak across sibling `prove:` blocks or out of nested parses
    /// that use this wrapper (`forall`, `exist`, `prove`, `prop` bodies, etc.).
    pub fn run_in_local_parsing_time_name_scope<T, E, F>(&mut self, f: F) -> Result<T, E>
    where
        F: FnOnce(&mut Self) -> Result<T, E>,
    {
        let saved_free_params = self.parsing_free_param_collection.clone();
        let result = f(self);
        self.parsing_free_param_collection = saved_free_params;
        result
    }

    /// `begin_scope` → `f` → `end_scope`; runs `end_scope` on both `Ok` and `Err` (not on `begin_scope` failure).
    pub fn parse_in_local_free_param_scope<T, F>(
        &mut self,
        kind: ParamObjType,
        names: &[String],
        line_file: LineFile,
        f: F,
    ) -> Result<T, RuntimeError>
    where
        F: FnOnce(&mut Self) -> Result<T, RuntimeError>,
    {
        self.parsing_free_param_collection
            .begin_scope(kind, names, line_file)?;
        let result = f(self);
        self.parsing_free_param_collection.end_scope(kind, names);
        result
    }

    /// If `names` is empty, runs `f` with no extra scope; otherwise wraps it in `parse_in_local_free_param_scope`.
    pub fn with_optional_free_param_scope<T, F>(
        &mut self,
        kind: ParamObjType,
        names: &[String],
        line_file: LineFile,
        f: F,
    ) -> Result<T, RuntimeError>
    where
        F: FnOnce(&mut Self) -> Result<T, RuntimeError>,
    {
        if names.is_empty() {
            f(self)
        } else {
            self.parse_in_local_free_param_scope(kind, names, line_file, f)
        }
    }

    pub fn parse_stmts_with_optional_free_param_scope<F>(
        &mut self,
        kind: ParamObjType,
        names: &[String],
        line_file: LineFile,
        parse_body: F,
    ) -> Result<Vec<Stmt>, RuntimeError>
    where
        F: FnOnce(&mut Self) -> Result<Vec<Stmt>, RuntimeError>,
    {
        self.with_optional_free_param_scope(kind, names, line_file, parse_body)
    }
}

impl Runtime {
    pub fn is_name_used_for_identifier_and_field_access(&self, name: &str) -> bool {
        if is_builtin_identifier_name(name) {
            return true;
        }

        for env in self.iter_environments_from_top() {
            if env.defined_identifiers.contains_key(name) {
                return true;
            }
        }

        false
    }

    pub fn is_name_used_for_prop(&self, name: &str) -> bool {
        return self.get_prop_definition_by_name(name).is_some();
    }

    pub fn is_name_used_for_abstract_prop(&self, name: &str) -> bool {
        if is_builtin_predicate(name) {
            return true;
        }

        return self.get_abstract_prop_definition_by_name(name).is_some();
    }

    pub fn is_name_used_for_family(&self, name: &str) -> bool {
        return self.get_family_definition_by_name(name).is_some();
    }

    pub fn is_name_used_for_algo(&self, name: &str) -> bool {
        return self.get_algo_definition_by_name(name).is_some();
    }
}

impl Runtime {
    pub fn new_file_and_update_runtime_with_file_content(&mut self, path: &str) {
        let path_rc: Rc<str> = Rc::from(path);
        self.module_manager.run_file_paths.push(path_rc.clone());
        self.module_manager.current_file_index = self.module_manager.run_file_paths.len() - 1;
        self.module_manager.display_entry_rc = Some(path_rc);
        self.module_manager.entry_path = path.to_string();
    }

    pub fn change_file_index_to(&mut self, file_index: usize) {
        self.module_manager.current_file_index = file_index;
    }
}

impl Runtime {
    pub fn store_tuple_obj_and_cart(
        &mut self,
        name: &str,
        tuple: Option<Tuple>,
        cart: Option<Cart>,
        line_file: LineFile,
    ) {
        let known_tuple_objs = &mut self.top_level_env().known_objs_equal_to_tuple;
        let old_tuple_and_cart = known_tuple_objs.get(name).cloned();

        let merged_tuple = match (tuple, old_tuple_and_cart.as_ref()) {
            (Some(new_tuple), _) => Some(new_tuple),
            (None, Some((old_tuple, _, _))) => old_tuple.clone(),
            (None, None) => None,
        };
        let merged_cart = match (cart, old_tuple_and_cart.as_ref()) {
            (Some(new_cart), _) => Some(new_cart),
            (None, Some((_, old_cart, _))) => old_cart.clone(),
            (None, None) => None,
        };
        let merged_line_file = line_file;

        known_tuple_objs.insert(
            name.to_string(),
            (merged_tuple, merged_cart, merged_line_file),
        );
    }

    pub fn store_known_cart_obj(&mut self, name: &str, cart: Cart, line_file: LineFile) {
        self.top_level_env()
            .known_objs_equal_to_cart
            .insert(name.to_string(), (cart, line_file));
    }

    pub fn store_known_finite_seq_list_obj(
        &mut self,
        name: &str,
        list: FiniteSeqListObj,
        member_of_finite_seq_set: Option<FiniteSeqSet>,
        line_file: LineFile,
    ) {
        let map = &mut self.top_level_env().known_objs_equal_to_finite_seq_list;
        let old = map.get(name).cloned();
        let merged_member = match (member_of_finite_seq_set, old.as_ref()) {
            (Some(new_s), _) => Some(new_s),
            (None, Some((_, Some(old_s), _))) => Some(old_s.clone()),
            (None, _) => None,
        };
        map.insert(name.to_string(), (list, merged_member, line_file));
    }

    pub fn store_known_matrix_list_obj(
        &mut self,
        name: &str,
        matrix: MatrixListObj,
        member_of_matrix_set: Option<MatrixSet>,
        line_file: LineFile,
    ) {
        let map = &mut self.top_level_env().known_objs_equal_to_matrix_list;
        let old = map.get(name).cloned();
        let merged_member = match (member_of_matrix_set, old.as_ref()) {
            (Some(new_s), _) => Some(new_s),
            (None, Some((_, Some(old_s), _))) => Some(old_s.clone()),
            (None, _) => None,
        };
        map.insert(name.to_string(), (matrix, merged_member, line_file));
    }

    pub fn matrix_set_to_fn_set(&self, ms: &MatrixSet, line_file: LineFile) -> FnSet {
        let pair = self.generate_random_unused_names(2);
        let p1 = pair[0].clone();
        let p2 = pair[1].clone();
        FnSet::new(
            vec![
                ParamGroupWithSet::new(vec![p1.clone()], StandardSet::NPos.into()),
                ParamGroupWithSet::new(vec![p2.clone()], StandardSet::NPos.into()),
            ],
            vec![
                AtomicFact::from(LessEqualFact::new(
                    obj_for_bound_param_in_scope(p1, ParamObjType::FnSet),
                    (*ms.row_len).clone(),
                    line_file.clone(),
                ))
                .into(),
                AtomicFact::from(LessEqualFact::new(
                    obj_for_bound_param_in_scope(p2, ParamObjType::FnSet),
                    (*ms.col_len).clone(),
                    line_file.clone(),
                ))
                .into(),
            ],
            (*ms.set).clone(),
        )
    }

    pub fn finite_seq_set_to_fn_set(&self, fs: &FiniteSeqSet, line_file: LineFile) -> FnSet {
        let param = self.generate_random_unused_name();
        FnSet::new(
            vec![ParamGroupWithSet::new(
                vec![param.clone()],
                StandardSet::NPos.into(),
            )],
            vec![AtomicFact::from(LessEqualFact::new(
                obj_for_bound_param_in_scope(param, ParamObjType::FnSet),
                (*fs.n).clone(),
                line_file,
            ))
            .into()],
            (*fs.set).clone(),
        )
    }

    pub fn seq_set_to_fn_set(&self, ss: &SeqSet, _line_file: LineFile) -> FnSet {
        let param = self.generate_random_unused_name();
        FnSet::new(
            vec![ParamGroupWithSet::new(
                vec![param.clone()],
                StandardSet::NPos.into(),
            )],
            vec![],
            (*ss.set).clone(),
        )
    }

    pub fn finite_seq_set_to_fn_set_from_surface_dom_param(
        &self,
        fs: &FiniteSeqSet,
        line_file: LineFile,
        surface_dom_param: &str,
    ) -> Result<FnSet, RuntimeError> {
        let params = vec![ParamGroupWithSet::new(
            vec![surface_dom_param.to_string()],
            StandardSet::NPos.into(),
        )];
        let dom_facts: Vec<OrAndChainAtomicFact> = vec![OrAndChainAtomicFact::AtomicFact(
            LessEqualFact::new(
                Identifier::new(surface_dom_param.to_string()).into(),
                (*fs.n).clone(),
                line_file,
            )
            .into(),
        )];
        self.new_fn_set(params, dom_facts, (*fs.set).clone())
    }

    pub fn store_well_defined_obj_cache(&mut self, obj: &Obj) {
        self.top_level_env()
            .cache_well_defined_obj
            .insert(obj.to_string(), ());
    }
}

impl Runtime {
    pub fn new_fn_set(
        &self,
        params_and_their_sets: Vec<ParamGroupWithSet>,
        dom_facts: Vec<OrAndChainAtomicFact>,
        ret_set: Obj,
    ) -> Result<FnSet, RuntimeError> {
        let empty: HashMap<String, Obj> = HashMap::new();
        let mut dom_stored = Vec::with_capacity(dom_facts.len());
        for d in &dom_facts {
            dom_stored.push(self.inst_or_and_chain_atomic_fact(d, &empty, ParamObjType::FnSet, None)?);
        }
        let ret_stored = self.inst_obj(&ret_set, &empty, ParamObjType::FnSet)?;
        Ok(FnSet::new(params_and_their_sets, dom_stored, ret_stored))
    }

    pub fn new_anonymous_fn(
        &self,
        params_and_their_sets: Vec<ParamGroupWithSet>,
        dom_facts: Vec<OrAndChainAtomicFact>,
        ret_set: Obj,
        equal_to: Obj,
    ) -> Result<AnonymousFn, RuntimeError> {
        let empty: HashMap<String, Obj> = HashMap::new();
        let mut dom_stored = Vec::with_capacity(dom_facts.len());
        for d in &dom_facts {
            dom_stored.push(
                self.inst_or_and_chain_atomic_fact(d, &empty, ParamObjType::FnSet, None)?,
            );
        }
        let ret_stored = self.inst_obj(&ret_set, &empty, ParamObjType::FnSet)?;
        let eq_stored = self.inst_obj(&equal_to, &empty, ParamObjType::FnSet)?;
        Ok(AnonymousFn::new(
            params_and_their_sets,
            dom_stored,
            ret_stored,
            eq_stored,
        ))
    }

    pub fn fn_set_from_fn_set_clause(&self, clause: &FnSetClause) -> Result<FnSet, RuntimeError> {
        self.new_fn_set(
            clause.params_def_with_set.clone(),
            clause.dom_facts.clone(),
            clause.ret_set.clone(),
        )
    }
}

impl Runtime {
    pub fn params_to_arg_map(
        &self,
        param_defs: &ParamDefWithType,
        args: &[Obj],
    ) -> Result<HashMap<String, Obj>, RuntimeError> {
        let param_names = param_defs.collect_param_names();
        if param_names.len() != args.len() {
            return Err(InstantiateRuntimeError(RuntimeErrorStruct::new(
                None,
                format!(
                    "params_to_arg_map: expected {} argument(s), got {}",
                    param_names.len(),
                    args.len()
                ),
                default_line_file(),
                None,
                vec![],
            ))
            .into());
        }

        let mut result: HashMap<String, Obj> = HashMap::new();
        for (param_name, arg) in param_names.iter().zip(args.iter()) {
            result.insert(param_name.clone(), arg.clone());
        }
        Ok(result)
    }
}
