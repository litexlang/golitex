use crate::prelude::*;

impl Runtime {
    pub fn iter_environments_from_top(&self) -> impl Iterator<Item = &Environment> {
        (0..self.environment_count()).map(|index| {
            self.environment_by_top_index(index)
                .expect("environment index should be valid")
        })
    }

    pub fn environment_count(&self) -> usize {
        let frame = self
            .execution_stack
            .last()
            .expect("an execution frame should always exist");
        let local_count = frame.local_environment_stack.len();
        match frame.layer {
            ExecutionLayer::Main => local_count + 1,
            ExecutionLayer::File(_) => local_count + 2,
        }
    }

    pub fn environment_by_top_index(&self, index: usize) -> Option<&Environment> {
        let frame = self.execution_stack.last()?;
        let local_count = frame.local_environment_stack.len();
        if index < local_count {
            return frame
                .local_environment_stack
                .get(local_count - 1 - index)
                .map(|environment| environment.as_ref());
        }
        let layer_index = index - local_count;
        match frame.layer {
            ExecutionLayer::Main => {
                let module = self.module_manager.module(frame.module_id)?;
                if layer_index == 0 {
                    return Some(module.main_environment.as_ref());
                }
                None
            }
            ExecutionLayer::File(current_file_id) => {
                let module = self.module_manager.module(frame.module_id)?;
                let current_file = module.file(current_file_id)?;
                if layer_index == 0 {
                    return Some(current_file.environment.as_ref());
                }
                if layer_index == 1 {
                    return Some(module.main_environment.as_ref());
                }
                None
            }
        }
    }

    pub fn is_symmetric_prop_name_known(&self, prop_name: &str) -> bool {
        for env in self.iter_environments_from_top() {
            if let Some(perms) = env.known_symmetric_props.get(prop_name) {
                if !perms.is_empty() {
                    return true;
                }
            }
        }
        false
    }

    pub fn get_object_in_fn_set(&self, obj: &Obj) -> Option<FnSetBody> {
        if let Some(info) = self.get_known_fn_info_for_obj(obj) {
            if let Some((body, _)) = info.fn_set.as_ref() {
                return Some(body.clone());
            }
        }

        None
    }

    pub fn get_cloned_object_in_fn_set(&self, obj: &Obj) -> Option<FnSetBody> {
        self.get_object_in_fn_set(obj)
    }

    pub fn get_cloned_object_in_fn_set_candidates(&self, obj: &Obj) -> Vec<FnSetBody> {
        self.get_cloned_object_in_fn_set(obj).into_iter().collect()
    }

    pub fn get_fn_range_function_body(&self, function: &Obj) -> Option<FnSetBody> {
        match function {
            Obj::AnonymousFn(anonymous_fn) => Some(anonymous_fn.body.clone()),
            _ => self.get_object_in_fn_set(function),
        }
    }

    /// User `have fn f … = …`: [`FnSetBody`] and defining RHS when both are stored in
    /// [`crate::environment::KnownFnInfo`] (inner scopes override outer).
    pub fn get_known_fn_body_and_equal_to_for_key(
        &self,
        key: &str,
    ) -> Option<(FnSetBody, Obj, LineFile)> {
        if let Some(info) = self.get_known_fn_info_for_key(key) {
            if let (Some((body, _lf_body)), Some((eq, eq_line))) =
                (info.fn_set.clone(), info.equal_to.clone())
            {
                return Some((body, eq, eq_line));
            }
        }
        None
    }

    pub(crate) fn unfold_known_fn_application_once(
        &mut self,
        application: &Obj,
        verify_state: &VerifyState,
    ) -> Result<Option<Obj>, RuntimeError> {
        let Obj::FnObj(fn_obj) = application else {
            return Ok(None);
        };
        if fn_obj.body.is_empty() {
            return Ok(None);
        }
        let key = match fn_obj.head.as_ref() {
            FnObjHead::Identifier(i) => i.to_string(),
            FnObjHead::IdentifierWithMod(i) => i.to_string(),
            _ => return Ok(None),
        };
        let Some((fn_set_body, equal_to_expr, _)) =
            self.get_known_fn_body_and_equal_to_for_key(key.as_str())
        else {
            return Ok(None);
        };

        let param_defs = &fn_set_body.params_def_with_set;
        let n_params = ParamGroupWithSet::number_of_params(param_defs);
        if n_params == 0 {
            return Ok(None);
        }
        let Some((args, extra_layers)) =
            split_fn_body_at_complete_layer_for_unfolding(&fn_obj.body, n_params)
        else {
            return Ok(None);
        };
        let param_to_arg_map =
            ParamGroupWithSet::param_defs_and_args_to_param_to_arg_map(param_defs, &args);

        let param_membership_facts =
            ParamGroupWithSet::facts_for_args_satisfy_param_def_with_set_vec(
                self,
                param_defs,
                &args,
                ParamObjType::FnSet,
            )?;
        for param_membership_fact in param_membership_facts.iter() {
            let result = self.verify_atomic_fact_by_known_atomic_or_builtin_only(
                param_membership_fact,
                verify_state,
            )?;
            if !result.is_true() {
                return Ok(None);
            }
        }
        for dom_fact in fn_set_body.dom_facts.iter() {
            let instantiated_dom_fact = self.inst_or_and_chain_atomic_fact(
                dom_fact,
                &param_to_arg_map,
                ParamObjType::FnSet,
                None,
            )?;
            let result = self.verify_or_and_chain_atomic_fact_by_known_atomic_or_builtin_only(
                &instantiated_dom_fact,
                verify_state,
            )?;
            if !result.is_true() {
                return Ok(None);
            }
        }

        let reduced = self.inst_obj(&equal_to_expr, &param_to_arg_map, ParamObjType::FnSet)?;
        Ok(apply_extra_curried_layers_for_unfolding(
            reduced,
            extra_layers,
        ))
    }

    fn get_known_fn_info_for_obj(&self, obj: &Obj) -> Option<KnownFnInfo> {
        let key = obj.to_string();
        if let Some(info) = self.get_known_fn_info_for_key_from_current_envs(&key) {
            return Some(info.clone());
        }

        if let Some((module_name, local_name)) = module_qualified_obj_name(obj) {
            return self.get_known_fn_info_for_module_qualified_name(module_name, local_name);
        }

        None
    }

    fn get_known_fn_info_for_key(&self, key: &str) -> Option<KnownFnInfo> {
        if let Some(info) = self.get_known_fn_info_for_key_from_current_envs(key) {
            return Some(info.clone());
        }

        if let Some((module_name, local_name)) = split_module_qualified_key(key) {
            return self.get_known_fn_info_for_module_qualified_name(module_name, local_name);
        }

        None
    }

    fn get_known_fn_info_for_key_from_current_envs(&self, key: &str) -> Option<&KnownFnInfo> {
        for env in self.iter_environments_from_top() {
            if let Some(info) = env.known_objs_in_fn_sets.get(key) {
                return Some(info);
            }
        }
        None
    }

    fn get_known_fn_info_for_module_qualified_name(
        &self,
        module_name: &str,
        local_name: &str,
    ) -> Option<KnownFnInfo> {
        let qualified_name =
            IdentifierWithMod::new(module_name.to_string(), local_name.to_string()).to_string();
        if self.is_current_parse_module(module_name) {
            return self
                .get_known_fn_info_for_key_from_current_envs(local_name)
                .or_else(|| self.get_known_fn_info_for_key_from_current_envs(&qualified_name))
                .cloned();
        }

        self.imported_module_environments(module_name)
            .into_iter()
            .find_map(|env| {
                env.known_objs_in_fn_sets
                    .get(local_name)
                    .or_else(|| env.known_objs_in_fn_sets.get(&qualified_name))
                    .cloned()
            })
    }

    pub fn cache_well_defined_obj_contains(&self, key: &str) -> bool {
        for env in self.iter_environments_from_top() {
            if env.cache_well_defined_obj.contains_key(key) {
                return true;
            }
        }
        false
    }

    pub fn cache_known_facts_contains(&self, key: &str) -> (bool, LineFile) {
        for env in self.iter_environments_from_top() {
            if let Some(line_file) = env.cache_known_fact.get(key) {
                return (true, line_file.clone());
            }
        }
        (false, default_line_file())
    }

    pub fn trust_summary_for_cached_fact(&self, key: &str) -> ProofTrustSummary {
        for env in self.iter_environments_from_top() {
            if let Some(summary) = env.cache_known_fact_trust.get(key) {
                return summary.clone();
            }
        }
        ProofTrustSummary::new()
    }

    pub fn get_object_equal_to_cart(&self, name: &str) -> Option<Cart> {
        for env in self.iter_environments_from_top() {
            if let Some((known_cart_obj, _)) = env.known_objs_equal_to_cart.get(name) {
                return Some(known_cart_obj.clone());
            }
            if let Some((_, Some(known_cart_obj), _)) = env.known_objs_equal_to_tuple.get(name) {
                return Some(known_cart_obj.clone());
            }
        }
        if let Some((module_name, local_name)) = split_module_qualified_key(name) {
            for env in self.imported_module_environments(module_name) {
                if let Some((known_cart_obj, _)) = env.known_objs_equal_to_cart.get(local_name) {
                    return Some(known_cart_obj.clone());
                }
                if let Some((_, Some(known_cart_obj), _)) =
                    env.known_objs_equal_to_tuple.get(local_name)
                {
                    return Some(known_cart_obj.clone());
                }
            }
        }
        None
    }

    pub fn get_obj_equal_to_set_builder(&self, name: &str) -> Option<SetBuilder> {
        for env in self.iter_environments_from_top() {
            if let Some((set_builder, _)) = env.known_objs_equal_to_set_builder.get(name) {
                return Some(set_builder.clone());
            }
        }
        if let Some((module_name, local_name)) = split_module_qualified_key(name) {
            for env in self.imported_module_environments(module_name) {
                if let Some((set_builder, _)) = env.known_objs_equal_to_set_builder.get(local_name)
                {
                    return Some(set_builder.clone());
                }
            }
        }
        None
    }

    pub fn get_obj_equal_to_tuple(&self, name: &str) -> Option<Tuple> {
        for env in self.iter_environments_from_top() {
            if let Some((Some(known_tuple_obj), _, _)) = env.known_objs_equal_to_tuple.get(name) {
                return Some(known_tuple_obj.clone());
            }
        }
        if let Some((module_name, local_name)) = split_module_qualified_key(name) {
            for env in self.imported_module_environments(module_name) {
                if let Some((Some(known_tuple_obj), _, _)) =
                    env.known_objs_equal_to_tuple.get(local_name)
                {
                    return Some(known_tuple_obj.clone());
                }
            }
        }
        None
    }

    pub fn get_obj_equal_to_finite_seq_list(&self, name: &str) -> Option<FiniteSeqListObj> {
        for env in self.iter_environments_from_top() {
            if let Some((known_list, _, _)) = env.known_objs_equal_to_finite_seq_list.get(name) {
                return Some(known_list.clone());
            }
        }
        if let Some((module_name, local_name)) = split_module_qualified_key(name) {
            for env in self.imported_module_environments(module_name) {
                if let Some((known_list, _, _)) =
                    env.known_objs_equal_to_finite_seq_list.get(local_name)
                {
                    return Some(known_list.clone());
                }
            }
        }
        None
    }

    pub fn get_finite_seq_set_for_obj_equal_to_seq_list(&self, name: &str) -> Option<FiniteSeqSet> {
        for env in self.iter_environments_from_top() {
            if let Some((_, member_of, _)) = env.known_objs_equal_to_finite_seq_list.get(name) {
                return member_of.clone();
            }
        }
        if let Some((module_name, local_name)) = split_module_qualified_key(name) {
            for env in self.imported_module_environments(module_name) {
                if let Some((_, member_of, _)) =
                    env.known_objs_equal_to_finite_seq_list.get(local_name)
                {
                    return member_of.clone();
                }
            }
        }
        None
    }

    pub fn get_obj_equal_to_matrix_list(&self, name: &str) -> Option<MatrixListObj> {
        for env in self.iter_environments_from_top() {
            if let Some((known_matrix, _, _)) = env.known_objs_equal_to_matrix_list.get(name) {
                return Some(known_matrix.clone());
            }
        }
        if let Some((module_name, local_name)) = split_module_qualified_key(name) {
            for env in self.imported_module_environments(module_name) {
                if let Some((known_matrix, _, _)) =
                    env.known_objs_equal_to_matrix_list.get(local_name)
                {
                    return Some(known_matrix.clone());
                }
            }
        }
        None
    }

    pub fn get_matrix_set_for_obj_equal_to_matrix_list(&self, name: &str) -> Option<MatrixSet> {
        for env in self.iter_environments_from_top() {
            if let Some((_, member_of, _)) = env.known_objs_equal_to_matrix_list.get(name) {
                return member_of.clone();
            }
        }
        if let Some((module_name, local_name)) = split_module_qualified_key(name) {
            for env in self.imported_module_environments(module_name) {
                if let Some((_, member_of, _)) = env.known_objs_equal_to_matrix_list.get(local_name)
                {
                    return member_of.clone();
                }
            }
        }
        None
    }

    pub fn get_object_equal_to_tuple(&self, name: &str) -> Option<Cart> {
        for env in self.iter_environments_from_top() {
            if let Some(cart) = env.known_objs_equal_to_tuple.get(name) {
                return cart.1.clone();
            }
        }
        if let Some((module_name, local_name)) = split_module_qualified_key(name) {
            for env in self.imported_module_environments(module_name) {
                if let Some(cart) = env.known_objs_equal_to_tuple.get(local_name) {
                    return cart.1.clone();
                }
            }
        }
        None
    }

    pub fn get_object_equal_to_normalized_decimal_number(&self, obj_str: &str) -> Option<Number> {
        for env in self.iter_environments_from_top() {
            if let Some(KnownObjValue::SimplifiedNumber(number)) = env.known_obj_values.get(obj_str)
            {
                return Some(number.clone());
            }
        }
        if let Some((module_name, local_name)) = split_module_qualified_key(obj_str) {
            for env in self.imported_module_environments(module_name) {
                if let Some(KnownObjValue::SimplifiedNumber(number)) =
                    env.known_obj_values.get(local_name)
                {
                    return Some(number.clone());
                }
            }
        }
        None
    }

    pub fn get_known_obj_value_as_obj(&self, obj_str: &str) -> Option<Obj> {
        for env in self.iter_environments_from_top() {
            if let Some(known_value) = env.known_obj_values.get(obj_str) {
                return match known_value {
                    KnownObjValue::SimplifiedNumber(number) => Some(number.clone().into()),
                    KnownObjValue::SimplifiedFraction(div) => Some(div.clone().into()),
                };
            }
        }
        if let Some((module_name, local_name)) = split_module_qualified_key(obj_str) {
            for env in self.imported_module_environments(module_name) {
                if let Some(known_value) = env.known_obj_values.get(local_name) {
                    return match known_value {
                        KnownObjValue::SimplifiedNumber(number) => Some(number.clone().into()),
                        KnownObjValue::SimplifiedFraction(div) => Some(div.clone().into()),
                    };
                }
            }
        }
        None
    }

    pub fn get_all_objs_equal_to_given(&self, given: &str) -> Vec<String> {
        let environments = self.iter_environments_from_top().collect::<Vec<_>>();
        Self::get_all_objs_equal_to_given_in_environments(&environments, given)
    }

    pub fn get_all_obj_representatives_equal_to_given(&self, given: &Obj) -> Vec<Obj> {
        let given_key = given.to_string();
        let mut result = Vec::new();
        let environments = self.iter_environments_from_top().collect::<Vec<_>>();
        Self::extend_obj_representatives_equal_to_given_in_environments(
            &mut result,
            &environments,
            std::slice::from_ref(&given_key),
        );

        if let Some((module_name, local_name)) = split_module_qualified_key(&given_key) {
            let lookup_environments = if self.is_current_parse_module(module_name) {
                environments
            } else {
                self.imported_module_environments(module_name)
            };
            Self::extend_obj_representatives_equal_to_given_in_environments(
                &mut result,
                &lookup_environments,
                &[given_key.clone(), local_name.to_string()],
            );
        }

        result.retain(|obj| obj.to_string() != given_key);
        result
    }

    fn extend_obj_representatives_equal_to_given_in_environments(
        result: &mut Vec<Obj>,
        environments: &[&Environment],
        initial_keys: &[String],
    ) {
        let mut keys = initial_keys.to_vec();
        let mut next_index = 0;
        while next_index < keys.len() {
            let current = keys[next_index].clone();
            next_index += 1;
            for environment in environments {
                let Some((_, equivalent_objects)) = environment.known_equality.get(&current) else {
                    continue;
                };
                for object in equivalent_objects.iter() {
                    let object_key = object.to_string();
                    if !keys.contains(&object_key) {
                        keys.push(object_key.clone());
                    }
                    if !result
                        .iter()
                        .any(|known_obj: &Obj| known_obj.to_string() == object_key)
                    {
                        result.push(object.clone());
                    }
                }
            }
        }
    }

    pub fn get_all_objs_equal_to_given_in_environment(
        environment: &Environment,
        given: &str,
    ) -> Vec<String> {
        Self::get_all_objs_equal_to_given_in_environments(&[environment], given)
    }

    pub(crate) fn get_all_objs_equal_to_given_in_environments(
        environments: &[&Environment],
        given: &str,
    ) -> Vec<String> {
        let mut result = vec![given.to_string()];
        let mut next_index = 0;
        let mut found_equality = false;

        while next_index < result.len() {
            let current = result[next_index].clone();
            next_index += 1;
            for environment in environments {
                let Some((_, equivalent_objects)) = environment.known_equality.get(&current) else {
                    continue;
                };
                found_equality = true;
                for object in equivalent_objects.iter() {
                    let object_key = object.to_string();
                    if !result.contains(&object_key) {
                        result.push(object_key);
                    }
                }
            }
        }

        if found_equality {
            result
        } else {
            vec![]
        }
    }

    pub fn imported_module_environments(&self, module_name: &str) -> Vec<&Environment> {
        if self.is_current_parse_module(module_name) {
            return vec![];
        }
        let target = self
            .module_manager
            .import_target_by_canonical_name(module_name);
        match target {
            Some(ImportTarget::Module(module_id)) => {
                let Some(module) = self.module_manager.module(module_id) else {
                    return vec![];
                };
                if let Some(file_id) = module.flattened_export_file {
                    return module
                        .file(file_id)
                        .filter(|file| file.status == FileStatus::Loaded)
                        .map(|file| vec![file.environment.as_ref()])
                        .unwrap_or_default();
                }
                vec![module.main_environment.as_ref()]
            }
            Some(ImportTarget::File { module_id, file_id }) => {
                let Some(module) = self.module_manager.module(module_id) else {
                    return vec![];
                };
                module
                    .file(file_id)
                    .filter(|file| file.status == FileStatus::Loaded)
                    .map(|file| vec![file.environment.as_ref()])
                    .unwrap_or_default()
            }
            None => vec![],
        }
    }

    pub fn is_current_parse_module(&self, module_name: &str) -> bool {
        self.current_parse_namespace()
            .is_some_and(|current_name| current_name == module_name)
    }

    pub fn current_parse_namespace(&self) -> Option<&str> {
        let frame = self.execution_stack.last()?;
        let module_id = frame.module_id;
        let module = self.module_manager.module(module_id)?;
        match frame.layer {
            ExecutionLayer::Main => {
                (!module.module_name.is_empty()).then_some(module.module_name.as_str())
            }
            ExecutionLayer::File(file_id) => {
                if module.flattened_export_file == Some(file_id) && !module.module_name.is_empty() {
                    return Some(module.module_name.as_str());
                }
                module
                    .file(file_id)
                    .map(|file| file.canonical_name.as_str())
                    .or_else(|| {
                        (!module.module_name.is_empty()).then_some(module.module_name.as_str())
                    })
            }
        }
    }

    pub fn atomic_fact_referenced_module_names(&self, atomic_fact: &AtomicFact) -> Vec<String> {
        let mut module_names = vec![];
        match atomic_fact {
            AtomicFact::NormalAtomicFact(f) => {
                collect_module_name_from_atomic_name(&f.predicate, &mut module_names);
            }
            AtomicFact::NotNormalAtomicFact(f) => {
                collect_module_name_from_atomic_name(&f.predicate, &mut module_names);
            }
            _ => {}
        }
        for arg in atomic_fact.args().iter() {
            collect_module_names_from_obj(arg, &mut module_names);
        }
        module_names
    }

    pub fn obj_referenced_module_names(&self, obj: &Obj) -> Vec<String> {
        let mut module_names = vec![];
        collect_module_names_from_obj(obj, &mut module_names);
        module_names
    }
}

fn split_fn_body_at_complete_layer_for_unfolding(
    body: &[Vec<Box<Obj>>],
    n_params: usize,
) -> Option<(Vec<Obj>, Vec<Vec<Box<Obj>>>)> {
    let mut args = Vec::new();
    let mut extra_layers = Vec::new();
    let mut consumed = 0;
    let mut outer_application_done = false;

    for layer in body.iter() {
        if outer_application_done {
            extra_layers.push(layer.clone());
            continue;
        }

        let next_consumed = consumed + layer.len();
        if next_consumed > n_params {
            return None;
        }

        for arg in layer.iter() {
            args.push((**arg).clone());
        }
        consumed = next_consumed;

        if consumed == n_params {
            outer_application_done = true;
        }
    }

    if consumed != n_params {
        return None;
    }

    Some((args, extra_layers))
}

fn apply_extra_curried_layers_for_unfolding(
    obj: Obj,
    extra_layers: Vec<Vec<Box<Obj>>>,
) -> Option<Obj> {
    if extra_layers.is_empty() {
        return Some(obj);
    }

    match obj {
        Obj::AnonymousFn(anonymous_fn) => Some(
            FnObj::new(
                FnObjHead::AnonymousFnLiteral(Box::new(anonymous_fn)),
                extra_layers,
            )
            .into(),
        ),
        Obj::Atom(atom) => {
            let head = FnObjHead::given_an_atom_return_a_fn_obj_head(Obj::Atom(atom))?;
            Some(FnObj::new(head, extra_layers).into())
        }
        Obj::FnObj(mut fn_obj) => {
            fn_obj.body.extend(extra_layers);
            Some(fn_obj.into())
        }
        _ => None,
    }
}

fn push_module_name(module_names: &mut Vec<String>, module_name: &str) {
    if !module_names.iter().any(|name| name == module_name) {
        module_names.push(module_name.to_string());
    }
}

fn module_qualified_obj_name(obj: &Obj) -> Option<(&str, &str)> {
    if let Obj::Atom(AtomObj::IdentifierWithMod(identifier)) = obj {
        return Some((identifier.mod_name.as_str(), identifier.name.as_str()));
    }
    None
}

fn split_module_qualified_key(key: &str) -> Option<(&str, &str)> {
    key.rsplit_once(MOD_SIGN)
        .filter(|(module_name, local_name)| !module_name.is_empty() && !local_name.is_empty())
}

fn collect_module_name_from_atomic_name(name: &AtomicName, module_names: &mut Vec<String>) {
    if let AtomicName::WithMod(module_name, _) = name {
        push_module_name(module_names, module_name);
    }
}

fn collect_module_names_from_obj(obj: &Obj, module_names: &mut Vec<String>) {
    match obj {
        Obj::Atom(atom) => collect_module_names_from_atom(atom, module_names),
        Obj::FnObj(fn_obj) => {
            collect_module_names_from_fn_obj_head(&fn_obj.head, module_names);
            for group in fn_obj.body.iter() {
                for arg in group.iter() {
                    collect_module_names_from_obj(arg, module_names);
                }
            }
        }
        Obj::Add(x) => collect_module_names_from_two(&x.left, &x.right, module_names),
        Obj::Sub(x) => collect_module_names_from_two(&x.left, &x.right, module_names),
        Obj::Mul(x) => collect_module_names_from_two(&x.left, &x.right, module_names),
        Obj::Div(x) => collect_module_names_from_two(&x.left, &x.right, module_names),
        Obj::Mod(x) => collect_module_names_from_two(&x.left, &x.right, module_names),
        Obj::IntegerQuotient(x) => {
            collect_module_names_from_two(&x.dividend, &x.divisor, module_names)
        }
        Obj::Pow(x) => collect_module_names_from_two(&x.base, &x.exponent, module_names),
        Obj::Log(x) => collect_module_names_from_two(&x.base, &x.arg, module_names),
        Obj::Max(x) => collect_module_names_from_two(&x.left, &x.right, module_names),
        Obj::Min(x) => collect_module_names_from_two(&x.left, &x.right, module_names),
        Obj::Union(x) => collect_module_names_from_two(&x.left, &x.right, module_names),
        Obj::Intersect(x) => collect_module_names_from_two(&x.left, &x.right, module_names),
        Obj::SetMinus(x) => collect_module_names_from_two(&x.left, &x.right, module_names),
        Obj::SetDiff(x) => collect_module_names_from_two(&x.left, &x.right, module_names),
        Obj::Range(x) => collect_module_names_from_two(&x.start, &x.end, module_names),
        Obj::ClosedRange(x) => collect_module_names_from_two(&x.start, &x.end, module_names),
        Obj::IntervalObj(x) => collect_module_names_from_two(x.start(), x.end(), module_names),
        Obj::MatrixAdd(x) => collect_module_names_from_two(&x.left, &x.right, module_names),
        Obj::MatrixSub(x) => collect_module_names_from_two(&x.left, &x.right, module_names),
        Obj::MatrixMul(x) => collect_module_names_from_two(&x.left, &x.right, module_names),
        Obj::MatrixScalarMul(x) => {
            collect_module_names_from_two(&x.scalar, &x.matrix, module_names)
        }
        Obj::MatrixPow(x) => collect_module_names_from_two(&x.base, &x.exponent, module_names),
        Obj::Proj(x) => collect_module_names_from_two(&x.set, &x.dim, module_names),
        Obj::ObjAtIndex(x) => collect_module_names_from_two(&x.obj, &x.index, module_names),
        Obj::FiniteSeqSet(x) => collect_module_names_from_two(&x.set, &x.n, module_names),
        Obj::MatrixSet(x) => {
            collect_module_names_from_obj(&x.set, module_names);
            collect_module_names_from_obj(&x.row_len, module_names);
            collect_module_names_from_obj(&x.col_len, module_names);
        }
        Obj::Sum(x) => {
            collect_module_names_from_obj(&x.start, module_names);
            collect_module_names_from_obj(&x.end, module_names);
            collect_module_names_from_obj(&x.func, module_names);
        }
        Obj::SumOfFiniteSet(x) => {
            collect_module_names_from_obj(&x.set, module_names);
            collect_module_names_from_obj(&x.func, module_names);
        }
        Obj::Product(x) => {
            collect_module_names_from_obj(&x.start, module_names);
            collect_module_names_from_obj(&x.end, module_names);
            collect_module_names_from_obj(&x.func, module_names);
        }
        Obj::ProductOfFiniteSet(x) => {
            collect_module_names_from_obj(&x.set, module_names);
            collect_module_names_from_obj(&x.func, module_names);
        }
        Obj::Abs(x) => collect_module_names_from_obj(&x.arg, module_names),
        Obj::Sqrt(x) => collect_module_names_from_obj(&x.arg, module_names),
        Obj::Cup(x) => collect_module_names_from_obj(&x.left, module_names),
        Obj::Cap(x) => collect_module_names_from_obj(&x.left, module_names),
        Obj::PowerSet(x) => collect_module_names_from_obj(&x.set, module_names),
        Obj::FiniteSetSize(x) => collect_module_names_from_obj(&x.set, module_names),
        Obj::FnRange(x) => collect_module_names_from_obj(&x.function, module_names),
        Obj::Replacement(x) => {
            collect_module_name_from_atomic_name(&x.prop_name, module_names);
            collect_module_names_from_obj(&x.source_set, module_names);
        }
        Obj::TupleDim(x) => collect_module_names_from_obj(&x.arg, module_names),
        Obj::CartDim(x) => collect_module_names_from_obj(&x.set, module_names),
        Obj::OneSideInfinityIntervalObj(x) => {
            collect_module_names_from_obj(x.start(), module_names)
        }
        Obj::SeqSet(x) => collect_module_names_from_obj(&x.set, module_names),
        Obj::ListSet(x) => {
            for obj in x.list.iter() {
                collect_module_names_from_obj(obj, module_names);
            }
        }
        Obj::GeneralCart(x) => {
            collect_module_names_from_obj(&x.index_set, module_names);
            collect_module_names_from_obj(&x.family_set, module_names);
            collect_module_names_from_obj(&x.family_fn, module_names);
        }
        Obj::Cart(x) => {
            for obj in x.args.iter() {
                collect_module_names_from_obj(obj, module_names);
            }
        }
        Obj::Tuple(x) => {
            for obj in x.args.iter() {
                collect_module_names_from_obj(obj, module_names);
            }
        }
        Obj::FiniteSeqListObj(x) => {
            for obj in x.objs.iter() {
                collect_module_names_from_obj(obj, module_names);
            }
        }
        Obj::MatrixListObj(x) => {
            for row in x.rows.iter() {
                for obj in row.iter() {
                    collect_module_names_from_obj(obj, module_names);
                }
            }
        }
        Obj::SetBuilder(x) => {
            collect_module_names_from_obj(&x.param_set, module_names);
            for fact in x.facts.iter() {
                collect_module_names_from_exist_body_fact(fact, module_names);
            }
        }
        Obj::FnSet(x) => collect_module_names_from_fn_set_body(&x.body, module_names),
        Obj::AnonymousFn(x) => {
            collect_module_names_from_fn_set_body(&x.body, module_names);
            collect_module_names_from_obj(&x.equal_to, module_names);
        }
        Obj::StructObj(x) => {
            collect_module_name_from_atomic_name(&x.name, module_names);
            for param in x.params.iter() {
                collect_module_names_from_obj(param, module_names);
            }
        }
        Obj::ObjAsStructInstanceWithFieldAccess(x) => {
            collect_module_name_from_atomic_name(&x.struct_obj.name, module_names);
            for param in x.struct_obj.params.iter() {
                collect_module_names_from_obj(param, module_names);
            }
            collect_module_names_from_obj(&x.obj, module_names);
        }
        Obj::InstantiatedTemplateObj(x) => {
            collect_module_name_from_atomic_name(&x.template_name, module_names);
            for arg in x.args.iter() {
                collect_module_names_from_obj(arg, module_names);
            }
        }
        Obj::Number(_) | Obj::StandardSet(_) => {}
    }
}

fn collect_module_names_from_atom(atom: &AtomObj, module_names: &mut Vec<String>) {
    if let AtomObj::IdentifierWithMod(identifier) = atom {
        push_module_name(module_names, &identifier.mod_name);
    }
}

fn collect_module_names_from_fn_obj_head(head: &FnObjHead, module_names: &mut Vec<String>) {
    match head {
        FnObjHead::IdentifierWithMod(identifier) => {
            push_module_name(module_names, &identifier.mod_name);
        }
        FnObjHead::AnonymousFnLiteral(anonymous_fn) => {
            collect_module_names_from_fn_set_body(&anonymous_fn.body, module_names);
            collect_module_names_from_obj(&anonymous_fn.equal_to, module_names);
        }
        FnObjHead::FiniteSeqListObj(list) => {
            for obj in list.objs.iter() {
                collect_module_names_from_obj(obj, module_names);
            }
        }
        FnObjHead::ObjAtIndex(obj_at_index) => {
            collect_module_names_from_obj(&obj_at_index.obj, module_names);
            collect_module_names_from_obj(&obj_at_index.index, module_names);
        }
        FnObjHead::ObjAsStructInstanceWithFieldAccess(field_access) => {
            collect_module_name_from_atomic_name(&field_access.struct_obj.name, module_names);
            for param in field_access.struct_obj.params.iter() {
                collect_module_names_from_obj(param, module_names);
            }
            collect_module_names_from_obj(&field_access.obj, module_names);
        }
        FnObjHead::InstantiatedTemplateObj(template_obj) => {
            collect_module_name_from_atomic_name(&template_obj.template_name, module_names);
            for arg in template_obj.args.iter() {
                collect_module_names_from_obj(arg, module_names);
            }
        }
        FnObjHead::Identifier(_)
        | FnObjHead::Forall(_)
        | FnObjHead::DefHeader(_)
        | FnObjHead::Exist(_)
        | FnObjHead::SetBuilder(_)
        | FnObjHead::FnSet(_)
        | FnObjHead::DefStructField(_)
        | FnObjHead::Induc(_)
        | FnObjHead::DefAlgo(_)
        | FnObjHead::TupleIndex(_)
        | FnObjHead::CartIndex(_) => {}
    }
}

fn collect_module_names_from_fn_set_body(body: &FnSetBody, module_names: &mut Vec<String>) {
    for group in body.params_def_with_set.iter() {
        collect_module_names_from_obj(group.set_obj(), module_names);
    }
    for fact in body.dom_facts.iter() {
        collect_module_names_from_or_and_chain_atomic_fact(fact, module_names);
    }
    collect_module_names_from_obj(&body.ret_set, module_names);
}

fn collect_module_names_from_or_and_chain_atomic_fact(
    fact: &OrAndChainAtomicFact,
    module_names: &mut Vec<String>,
) {
    match fact {
        OrAndChainAtomicFact::AtomicFact(fact) => {
            collect_module_names_from_atomic_fact(fact, module_names);
        }
        OrAndChainAtomicFact::AndFact(fact) => {
            for atomic_fact in fact.facts.iter() {
                collect_module_names_from_atomic_fact(atomic_fact, module_names);
            }
        }
        OrAndChainAtomicFact::ChainFact(fact) => {
            for name in fact.prop_names.iter() {
                collect_module_name_from_atomic_name(name, module_names);
            }
            for obj in fact.objs.iter() {
                collect_module_names_from_obj(obj, module_names);
            }
        }
        OrAndChainAtomicFact::OrFact(fact) => {
            for branch in fact.facts.iter() {
                collect_module_names_from_and_chain_atomic_fact(branch, module_names);
            }
        }
    }
}

fn collect_module_names_from_exist_body_fact(fact: &ExistBodyFact, module_names: &mut Vec<String>) {
    match fact {
        ExistBodyFact::AtomicFact(fact) => {
            collect_module_names_from_atomic_fact(fact, module_names);
        }
        ExistBodyFact::AndFact(fact) => {
            for atomic_fact in fact.facts.iter() {
                collect_module_names_from_atomic_fact(atomic_fact, module_names);
            }
        }
        ExistBodyFact::ChainFact(fact) => {
            for name in fact.prop_names.iter() {
                collect_module_name_from_atomic_name(name, module_names);
            }
            for obj in fact.objs.iter() {
                collect_module_names_from_obj(obj, module_names);
            }
        }
        ExistBodyFact::OrFact(fact) => {
            for branch in fact.facts.iter() {
                collect_module_names_from_and_chain_atomic_fact(branch, module_names);
            }
        }
        ExistBodyFact::InlineForall(forall_fact) => {
            collect_module_names_from_param_def_with_type(
                &forall_fact.params_def_with_type,
                module_names,
            );
            for fact in forall_fact.dom_facts.iter() {
                collect_module_names_from_fact(fact, module_names);
            }
            for fact in forall_fact.then_facts.iter() {
                collect_module_names_from_exist_or_and_chain_atomic_fact(fact, module_names);
            }
        }
    }
}

fn collect_module_names_from_and_chain_atomic_fact(
    fact: &AndChainAtomicFact,
    module_names: &mut Vec<String>,
) {
    match fact {
        AndChainAtomicFact::AtomicFact(fact) => {
            collect_module_names_from_atomic_fact(fact, module_names);
        }
        AndChainAtomicFact::AndFact(fact) => {
            for atomic_fact in fact.facts.iter() {
                collect_module_names_from_atomic_fact(atomic_fact, module_names);
            }
        }
        AndChainAtomicFact::ChainFact(fact) => {
            for name in fact.prop_names.iter() {
                collect_module_name_from_atomic_name(name, module_names);
            }
            for obj in fact.objs.iter() {
                collect_module_names_from_obj(obj, module_names);
            }
        }
    }
}

fn collect_module_names_from_atomic_fact(fact: &AtomicFact, module_names: &mut Vec<String>) {
    match fact {
        AtomicFact::NormalAtomicFact(fact) => {
            collect_module_name_from_atomic_name(&fact.predicate, module_names);
        }
        AtomicFact::NotNormalAtomicFact(fact) => {
            collect_module_name_from_atomic_name(&fact.predicate, module_names);
        }
        _ => {}
    }
    for arg in fact.args().iter() {
        collect_module_names_from_obj(arg, module_names);
    }
}

fn collect_module_names_from_exist_or_and_chain_atomic_fact(
    fact: &ExistOrAndChainAtomicFact,
    module_names: &mut Vec<String>,
) {
    match fact {
        ExistOrAndChainAtomicFact::AtomicFact(fact) => {
            collect_module_names_from_atomic_fact(fact, module_names);
        }
        ExistOrAndChainAtomicFact::AndFact(fact) => {
            for atomic_fact in fact.facts.iter() {
                collect_module_names_from_atomic_fact(atomic_fact, module_names);
            }
        }
        ExistOrAndChainAtomicFact::ChainFact(fact) => {
            for name in fact.prop_names.iter() {
                collect_module_name_from_atomic_name(name, module_names);
            }
            for obj in fact.objs.iter() {
                collect_module_names_from_obj(obj, module_names);
            }
        }
        ExistOrAndChainAtomicFact::OrFact(fact) => {
            for branch in fact.facts.iter() {
                collect_module_names_from_and_chain_atomic_fact(branch, module_names);
            }
        }
        ExistOrAndChainAtomicFact::ExistFact(fact) => {
            collect_module_names_from_exist_fact(fact, module_names);
        }
    }
}

fn collect_module_names_from_fact(fact: &Fact, module_names: &mut Vec<String>) {
    match fact {
        Fact::AtomicFact(fact) => collect_module_names_from_atomic_fact(fact, module_names),
        Fact::ExistFact(fact) => collect_module_names_from_exist_fact(fact, module_names),
        Fact::OrFact(fact) => {
            for branch in fact.facts.iter() {
                collect_module_names_from_and_chain_atomic_fact(branch, module_names);
            }
        }
        Fact::AndFact(fact) => {
            for atomic_fact in fact.facts.iter() {
                collect_module_names_from_atomic_fact(atomic_fact, module_names);
            }
        }
        Fact::ChainFact(fact) => {
            for name in fact.prop_names.iter() {
                collect_module_name_from_atomic_name(name, module_names);
            }
            for obj in fact.objs.iter() {
                collect_module_names_from_obj(obj, module_names);
            }
        }
        Fact::ForallFact(fact) => collect_module_names_from_forall_fact(fact, module_names),
        Fact::ForallFactWithIff(fact) => {
            collect_module_names_from_forall_fact(&fact.forall_fact, module_names);
            for iff_fact in fact.iff_facts.iter() {
                collect_module_names_from_exist_or_and_chain_atomic_fact(iff_fact, module_names);
            }
        }
        Fact::NotForall(fact) => {
            collect_module_names_from_forall_fact(&fact.forall_fact, module_names)
        }
    }
}

fn collect_module_names_from_forall_fact(fact: &ForallFact, module_names: &mut Vec<String>) {
    collect_module_names_from_param_def_with_type(&fact.params_def_with_type, module_names);
    for dom_fact in fact.dom_facts.iter() {
        collect_module_names_from_fact(dom_fact, module_names);
    }
    for then_fact in fact.then_facts.iter() {
        collect_module_names_from_exist_or_and_chain_atomic_fact(then_fact, module_names);
    }
}

fn collect_module_names_from_exist_fact(fact: &ExistFactEnum, module_names: &mut Vec<String>) {
    let body = fact.body();
    collect_module_names_from_param_def_with_type(&body.params_def_with_type, module_names);
    for body_fact in body.facts.iter() {
        collect_module_names_from_exist_body_fact(body_fact, module_names);
    }
}

fn collect_module_names_from_param_def_with_type(
    param_def: &ParamDefWithType,
    module_names: &mut Vec<String>,
) {
    for group in param_def.groups.iter() {
        if let ParamType::Obj(obj) = &group.param_type {
            collect_module_names_from_obj(obj, module_names);
        }
    }
}

fn collect_module_names_from_two(left: &Obj, right: &Obj, module_names: &mut Vec<String>) {
    collect_module_names_from_obj(left, module_names);
    collect_module_names_from_obj(right, module_names);
}
