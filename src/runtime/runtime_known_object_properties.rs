use crate::prelude::*;
use std::collections::HashSet;
use std::rc::Rc;

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
        if let Some(body) = self.get_direct_object_in_fn_set(obj) {
            return Some(body);
        }

        // Equality transports callable shape. For example, after `g = f`, a
        // stored signature for `f` also makes `g(a)` eligible for the ordinary
        // domain check. This is a bounded lookup over stored representatives;
        // it does not enter equality proof search from well-definedness.
        for representative in self.get_all_obj_representatives_equal_to_given(obj) {
            if let Some(body) = self.get_direct_object_in_fn_set(&representative) {
                return Some(body);
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
    pub fn get_known_fn_body_and_equal_to_for_obj(
        &self,
        obj: &Obj,
    ) -> Option<(FnSetBody, Obj, LineFile)> {
        if let Some(info) = self.get_known_fn_info_for_obj(obj) {
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
        verify_state: &UseContextVerifyState,
    ) -> Result<Option<Obj>, RuntimeError> {
        self.unfold_known_fn_application_once_impl(application, verify_state, true)
    }

    /// Reduce only a definition attached directly to the submitted
    /// application. This route neither materializes a new template instance
    /// nor searches equality representatives for another function definition.
    pub(crate) fn reduce_direct_known_fn_application_once(
        &mut self,
        application: &Obj,
        verify_state: &UseContextVerifyState,
    ) -> Result<Option<Obj>, RuntimeError> {
        self.unfold_known_fn_application_once_impl(application, verify_state, false)
    }

    fn unfold_known_fn_application_once_impl(
        &mut self,
        application: &Obj,
        verify_state: &UseContextVerifyState,
        allow_indirect_lookup: bool,
    ) -> Result<Option<Obj>, RuntimeError> {
        let Obj::FnObj(fn_obj) = application else {
            return Ok(None);
        };
        if fn_obj.body.is_empty() {
            return Ok(None);
        }
        // A callable tuple projection unfolds through a known tuple value.
        // Example: `&Pair{\selected<a>}.second(x)` reduces when
        // `\selected<a> = (first_value, fn(t T) U {...})` is known.
        let callable_projection = match fn_obj.head.as_ref() {
            FnObjHead::ObjAsStructInstanceWithFieldAccess(field_access) => Some((
                field_access.obj.as_ref().clone(),
                self.struct_field_index(&field_access.struct_obj, &field_access.field_name)?,
            )),
            FnObjHead::ObjAtIndex(obj_at_index) => {
                let index = self
                    .resolve_obj_to_number(obj_at_index.index.as_ref())
                    .and_then(|number| number.normalized_value.parse::<usize>().ok());
                index.map(|index| (obj_at_index.obj.as_ref().clone(), index))
            }
            _ => None,
        };
        if let Some((struct_value_obj, index)) = callable_projection {
            if let Obj::InstantiatedTemplateObj(template_obj) = &struct_value_obj {
                if !self.is_name_used_for_identifier(&template_obj.surface_name()) {
                    if !allow_indirect_lookup
                        || self
                            .materialize_instantiated_template_obj(template_obj, verify_state)
                            .is_err()
                    {
                        return Ok(None);
                    }
                }
            }
            let mut struct_values = vec![struct_value_obj.clone()];
            if let Some(unfolded_struct_value) = self.unfold_known_fn_application_once_impl(
                &struct_value_obj,
                verify_state,
                allow_indirect_lookup,
            )? {
                struct_values.push(unfolded_struct_value);
            }
            if allow_indirect_lookup {
                let key = obj_equality_key(&struct_value_obj);
                for env in self.iter_environments_from_top() {
                    if let Some((_, equal_objs)) = env.known_equality.get(&key) {
                        struct_values.extend(equal_objs.iter().cloned());
                    }
                }
            }
            for struct_value in struct_values {
                // Most structure values are already literal tuples. Project
                // those immediately; only a non-tuple callable constructor can
                // benefit from the one checked-constructor unfold below.
                let constructor = match struct_value {
                    Obj::Tuple(tuple) => Some(Obj::Tuple(tuple)),
                    Obj::FnObj(_) | Obj::InstantiatedTemplateObj(_) => self
                        .unfold_known_fn_application_once_impl(
                            &struct_value,
                            verify_state,
                            allow_indirect_lookup,
                        )?,
                    _ => None,
                };
                let Some(Obj::Tuple(tuple)) = constructor else {
                    continue;
                };
                let Some(field_value) = tuple.args.get(index - 1) else {
                    continue;
                };
                if let Some(applied) = apply_extra_curried_layers_for_unfolding(
                    field_value.as_ref().clone(),
                    fn_obj.body.clone(),
                ) {
                    return Ok(Some(applied));
                }
            }
            return Ok(None);
        }
        if let FnObjHead::InstantiatedTemplateObj(template_obj) = fn_obj.head.as_ref() {
            // One-step unfolding is a best-effort search operation. Equality
            // classes and owner indexes can retain a function application
            // whose template arguments belonged to a closed local binder
            // scope. That candidate cannot be unfolded now, but it must not
            // abort unrelated verification. Direct uses of an ill-defined
            // template are still rejected by the caller's ordinary WD check.
            if !self.is_name_used_for_identifier(&template_obj.surface_name()) {
                if !allow_indirect_lookup
                    || self
                        .materialize_instantiated_template_obj(template_obj, verify_state)
                        .is_err()
                {
                    return Ok(None);
                }
            }
        }
        let function_name_obj: Obj = match fn_obj.head.as_ref() {
            FnObjHead::Identifier(_)
            | FnObjHead::IdentifierWithMod(_)
            | FnObjHead::InstantiatedTemplateObj(_) => (*fn_obj.head).clone().into(),
            _ => return Ok(None),
        };
        let direct_definition = self.get_known_fn_body_and_equal_to_for_obj(&function_name_obj);
        let known_definition = if allow_indirect_lookup {
            direct_definition.or_else(|| {
                self.get_all_obj_representatives_equal_to_given(&function_name_obj)
                    .into_iter()
                    .find_map(|representative| {
                        let info = self.get_known_fn_info_for_obj(&representative)?;
                        match (info.fn_set, info.equal_to) {
                            (Some((body, _)), Some((equal_to, line_file))) => {
                                Some((body, equal_to, line_file))
                            }
                            _ => None,
                        }
                    })
            })
        } else {
            direct_definition
        };
        let Some((fn_set_body, equal_to_expr, _)) = known_definition else {
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

        if !verify_state.well_defined_already_verified {
            let param_membership_facts =
                ParamGroupWithSet::facts_for_args_satisfy_param_def_with_set_vec(
                    self,
                    param_defs,
                    &args,
                    ParamObjType::FnSet,
                )?;
            for param_membership_fact in param_membership_facts.iter() {
                let result = self.verify_atomic_fact_restricted_known_builtin(
                    param_membership_fact,
                    verify_state,
                )?;
                if !result.is_true() {
                    return Ok(None);
                }
            }
            for dom_fact in fn_set_body.dom_facts.iter() {
                let instantiated_dom_fact = self.inst_quantifier_free_fact(
                    dom_fact,
                    &param_to_arg_map,
                    ParamObjType::FnSet,
                    None,
                )?;
                let result = self.verify_quantifier_free_fact_restricted_known_builtin(
                    &instantiated_dom_fact,
                    verify_state,
                )?;
                if !result.is_true() {
                    return Ok(None);
                }
            }
        }

        let reduced = self.inst_obj(&equal_to_expr, &param_to_arg_map, ParamObjType::FnSet)?;
        Ok(apply_extra_curried_layers_for_unfolding(
            reduced,
            extra_layers,
        ))
    }

    /// Follow a short chain of checked `have fn` definitions until its value is
    /// a set builder. This is intentionally bounded: it exposes a declared
    /// carrier through set-valued function families without turning definition
    /// unfolding into unbounded proof search.
    pub(crate) fn unfold_known_fn_application_to_set_builder(
        &mut self,
        application: &Obj,
        verify_state: &UseContextVerifyState,
    ) -> Result<Option<SetBuilder>, RuntimeError> {
        const MAX_SET_BUILDER_UNFOLD_DEPTH: usize = 8;

        let mut current = application.clone();
        let mut seen = std::collections::HashSet::new();
        for _ in 0..MAX_SET_BUILDER_UNFOLD_DEPTH {
            if let Obj::SetBuilder(set_builder) = &current {
                return Ok(Some(set_builder.clone()));
            }
            if let Some(set_builder) = self.get_obj_equal_to_set_builder(&current) {
                return Ok(Some(set_builder));
            }
            if !seen.insert(obj_equality_key(&current)) {
                return Ok(None);
            }
            let next = match self.unfold_known_fn_application_once(&current, verify_state)? {
                Some(next) => Some(next),
                None => self.beta_reduce_complete_anonymous_application_once(&current)?,
            };
            let Some(next) = next else {
                return Ok(None);
            };
            current = next;
        }
        Ok(None)
    }

    /// Capture-avoiding beta reduction for one complete anonymous-function
    /// application layer. Any remaining curried application layers are kept on
    /// the substituted result when that result is callable.
    pub(crate) fn beta_reduce_complete_anonymous_application_once(
        &self,
        application: &Obj,
    ) -> Result<Option<Obj>, RuntimeError> {
        let Obj::FnObj(fn_obj) = application else {
            return Ok(None);
        };
        let FnObjHead::AnonymousFnLiteral(anonymous_fn) = fn_obj.head.as_ref() else {
            return Ok(None);
        };
        let param_defs = &anonymous_fn.body.params_def_with_set;
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
        let reduced = self.inst_obj(
            anonymous_fn.equal_to.as_ref(),
            &param_to_arg_map,
            ParamObjType::FnSet,
        )?;
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

        for module_name in self.obj_referenced_module_names(obj) {
            if self.is_current_parse_module(&module_name) {
                continue;
            }
            for env in self.imported_module_environments(&module_name) {
                if let Some(info) = env.known_objs_in_fn_sets.get(&key) {
                    return Some(info.clone());
                }
            }
        }

        if let Some((module_name, local_name)) = module_qualified_obj_name(obj) {
            return self.get_known_fn_info_for_module_qualified_name(module_name, local_name);
        }

        None
    }

    fn get_direct_object_in_fn_set(&self, obj: &Obj) -> Option<FnSetBody> {
        let info = self.get_known_fn_info_for_obj(obj)?;
        info.fn_set.map(|(body, _)| body)
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
        let key = WellDefinedCacheKey::without_function_contract(key.to_string());
        self.well_defined_cache_entry(&key).is_some()
    }

    pub(crate) fn well_defined_cache_key_for_obj(&self, obj: &Obj) -> Option<WellDefinedCacheKey> {
        let mut contracts = Vec::new();
        if !self.collect_well_defined_function_contracts(obj, &mut contracts) {
            return None;
        }
        Some(WellDefinedCacheKey::new(obj.to_string(), contracts))
    }

    fn known_function_contract_for_obj(&self, obj: &Obj) -> Option<WellDefinedFunctionContract> {
        let contract_from_info = |key: &str, info: KnownFnInfo| {
            let (body, _) = info.fn_set?;
            Some(
                info.fn_set_membership_fact_id
                    .map(WellDefinedFunctionContract::StoredMembershipFact)
                    .unwrap_or_else(|| {
                        WellDefinedFunctionContract::Structural(format!("{}::{}", key, body))
                    }),
            )
        };
        if let Some(info) = self.get_known_fn_info_for_obj(obj) {
            if let Some(contract) = contract_from_info(&obj.to_string(), info) {
                return Some(contract);
            }
        }
        for representative in self.get_all_obj_representatives_equal_to_given(obj) {
            if let Some(info) = self.get_known_fn_info_for_obj(&representative) {
                if let Some(contract) = contract_from_info(&representative.to_string(), info) {
                    return Some(contract);
                }
            }
        }
        None
    }

    fn collect_well_defined_function_contracts(
        &self,
        obj: &Obj,
        contracts: &mut Vec<WellDefinedFunctionContract>,
    ) -> bool {
        if let Obj::FnObj(fn_obj) = obj {
            let head_is_cacheable =
                match fn_obj.head.as_ref() {
                    FnObjHead::AnonymousFnLiteral(_) => false,
                    FnObjHead::FiniteSeqListObj(list) => list.objs.iter().all(|child| {
                        self.collect_well_defined_function_contracts(child, contracts)
                    }),
                    FnObjHead::MatrixOperator(matrix) => {
                        self.collect_well_defined_function_contracts(matrix, contracts)
                    }
                    FnObjHead::ObjAsStructInstanceWithFieldAccess(field) => {
                        field.struct_obj.params.iter().all(|child| {
                            self.collect_well_defined_function_contracts(child, contracts)
                        }) && self.collect_well_defined_function_contracts(&field.obj, contracts)
                    }
                    head => {
                        let head_obj: Obj = head.clone().into();
                        let Some(contract) = self.known_function_contract_for_obj(&head_obj) else {
                            return false;
                        };
                        if !contracts.contains(&contract) {
                            contracts.push(contract);
                        }
                        self.collect_well_defined_function_contracts(&head_obj, contracts)
                    }
                };
            return head_is_cacheable
                && fn_obj.body.iter().flatten().all(|argument| {
                    self.collect_well_defined_function_contracts(argument, contracts)
                });
        }
        let mut collect =
            |child: &Obj| self.collect_well_defined_function_contracts(child, contracts);
        let mut collect_two = |left: &Obj, right: &Obj| collect(left) && collect(right);
        match obj {
            Obj::Atom(_)
            | Obj::Number(_)
            | Obj::ImaginaryUnit(_)
            | Obj::EulerNumber(_)
            | Obj::Pi(_)
            | Obj::StandardSet(_) => true,
            Obj::FnObj(_) => unreachable!("function objects returned before recursive dispatch"),
            Obj::Add(x) => collect_two(&x.left, &x.right),
            Obj::Sub(x) => collect_two(&x.left, &x.right),
            Obj::Mul(x) => collect_two(&x.left, &x.right),
            Obj::Div(x) => collect_two(&x.left, &x.right),
            Obj::Mod(x) => collect_two(&x.left, &x.right),
            Obj::Gcd(x) => collect_two(&x.left, &x.right),
            Obj::Lcm(x) => collect_two(&x.left, &x.right),
            Obj::Min(x) => collect_two(&x.left, &x.right),
            Obj::Max(x) => collect_two(&x.left, &x.right),
            Obj::Pow(x) => collect_two(&x.base, &x.exponent),
            Obj::Log(x) => collect_two(&x.base, &x.arg),
            Obj::Union(x) => collect_two(&x.left, &x.right),
            Obj::Intersect(x) => collect_two(&x.left, &x.right),
            Obj::SetMinus(x) => collect_two(&x.left, &x.right),
            Obj::Range(x) => collect_two(&x.start, &x.end),
            Obj::ClosedRange(x) => collect_two(&x.start, &x.end),
            Obj::IntervalObj(x) => collect_two(x.start(), x.end()),
            Obj::MatrixAdd(x) => collect_two(&x.left, &x.right),
            Obj::MatrixSub(x) => collect_two(&x.left, &x.right),
            Obj::MatrixMul(x) => collect_two(&x.left, &x.right),
            Obj::MatrixScalarMul(x) => collect_two(&x.scalar, &x.matrix),
            Obj::MatrixPow(x) => collect_two(&x.base, &x.exponent),
            Obj::Proj(x) => collect_two(&x.set, &x.dim),
            Obj::ObjAtIndex(x) => collect_two(&x.obj, &x.index),
            Obj::FiniteSeqSet(x) => collect_two(&x.set, &x.n),
            Obj::Exp(x) => collect(&x.arg),
            Obj::Ln(x) => collect(&x.arg),
            Obj::Sign(x) => collect(&x.arg),
            Obj::Factorial(x) => collect(&x.arg),
            Obj::RealPart(x) => collect(&x.arg),
            Obj::ImaginaryPart(x) => collect(&x.arg),
            Obj::ComplexAbs(x) => collect(&x.arg),
            Obj::Abs(x) => collect(&x.arg),
            Obj::Floor(x) => collect(&x.arg),
            Obj::Ceil(x) => collect(&x.arg),
            Obj::Sin(x) => collect(&x.arg),
            Obj::Cos(x) => collect(&x.arg),
            Obj::Tan(x) => collect(&x.arg),
            Obj::Cot(x) => collect(&x.arg),
            Obj::Sqrt(x) => collect(&x.arg),
            Obj::BigUnion(x) => collect(&x.left),
            Obj::BigIntersect(x) => collect(&x.left),
            Obj::PowerSet(x) => collect(&x.set),
            Obj::FiniteSetSize(x) => collect(&x.set),
            Obj::FiniteSetMax(x) => collect(&x.set),
            Obj::FiniteSetMin(x) => collect(&x.set),
            Obj::FnRange(x) => collect(&x.function),
            Obj::TupleDim(x) => collect(&x.arg),
            Obj::CartDim(x) => collect(&x.set),
            Obj::OneSideInfinityIntervalObj(x) => collect(x.start()),
            Obj::SeqSet(x) => collect(&x.set),
            Obj::Replacement(x) => collect(&x.source_set),
            Obj::MatrixSet(x) => collect(&x.set) && collect(&x.row_len) && collect(&x.col_len),
            Obj::Sum(x) => collect(&x.start) && collect(&x.end) && collect(&x.func),
            Obj::SumOfFiniteSet(x) => collect(&x.set) && collect(&x.func),
            Obj::Product(x) => collect(&x.start) && collect(&x.end) && collect(&x.func),
            Obj::ProductOfFiniteSet(x) => collect(&x.set) && collect(&x.func),
            Obj::Reduce(x) => [&x.start, &x.end, &x.func, &x.op, &x.seed]
                .into_iter()
                .all(|child| collect(child)),
            Obj::FiniteSetReduce(x) => [&x.set, &x.func, &x.op, &x.seed]
                .into_iter()
                .all(|child| collect(child)),
            Obj::ListSet(x) => x.list.iter().all(|child| collect(child)),
            Obj::GeneralCart(x) => {
                collect(&x.index_set) && collect(&x.family_set) && collect(&x.family_fn)
            }
            Obj::Cart(x) => x.args.iter().all(|child| collect(child)),
            Obj::Tuple(x) => x.args.iter().all(|child| collect(child)),
            Obj::FiniteSeqListObj(x) => x.objs.iter().all(|child| collect(child)),
            Obj::MatrixListObj(x) => x.rows.iter().flatten().all(|child| collect(child)),
            Obj::StructObj(x) => x.params.iter().all(|child| collect(child)),
            Obj::ObjAsStructInstanceWithFieldAccess(x) => {
                x.struct_obj.params.iter().all(|child| collect(child)) && collect(&x.obj)
            }
            Obj::InstantiatedTemplateObj(x) => x.args.iter().all(|child| collect(child)),
            // Their WD traversals open binder scopes and may contain facts
            // whose callable contracts are not children in the object AST.
            // Keep the environment proof, but deliberately do not reuse a
            // boolean/object cache entry for these binder-owning objects.
            Obj::SetBuilder(_) | Obj::FnSet(_) | Obj::AnonymousFn(_) => false,
        }
    }

    pub(crate) fn well_defined_cache_entry(
        &self,
        key: &WellDefinedCacheKey,
    ) -> Option<&CachedWellDefinedObj> {
        self.iter_environments_from_top()
            .find_map(|env| env.cache_well_defined_obj.get(key))
    }

    pub(crate) fn well_defined_obj_proof(
        &self,
        proof_id: WellDefinedObjId,
    ) -> Option<Rc<WellDefinedObjProof>> {
        self.iter_environments_from_top()
            .find_map(|env| env.well_defined_obj_proofs.get(&proof_id).cloned())
    }

    pub(crate) fn well_defined_fact_proof(
        &self,
        fact_id: WellDefinedFactId,
    ) -> Option<Rc<WellDefinedFactProof>> {
        self.iter_environments_from_top()
            .find_map(|env| env.well_defined_fact_proofs.get(&fact_id).cloned())
    }

    pub(crate) fn well_defined_fact_id_for_proof(
        &self,
        proof: &Rc<FactualStmtSuccess>,
    ) -> Option<WellDefinedFactId> {
        self.iter_environments_from_top().find_map(|env| {
            env.well_defined_fact_proofs.iter().find_map(|(id, known)| {
                if Rc::ptr_eq(&known.proof, proof) {
                    Some(*id)
                } else {
                    None
                }
            })
        })
    }

    pub fn cache_known_facts_contains(&self, key: &str) -> (bool, LineFile) {
        for env in self.iter_environments_from_top() {
            if let Some(cached_fact) = env.cache_known_fact.get(key) {
                return (true, cached_fact.line_file.clone());
            }
        }
        (false, default_line_file())
    }

    pub fn cached_known_fact(&self, key: &str) -> Option<&CachedKnownFact> {
        self.iter_environments_from_top()
            .find_map(|env| env.cache_known_fact.get(key))
    }

    pub fn known_fact_id(&self, key: &str) -> Option<FactId> {
        self.cached_known_fact(key).map(|cached| cached.fact_id)
    }

    pub fn known_fact_id_for_fact(&self, fact: &Fact) -> Result<Option<FactId>, RuntimeError> {
        let display_key = fact.to_string();
        if let Some(fact_id) = self.known_fact_id(&display_key) {
            return Ok(Some(fact_id));
        }
        let nested_key = nested_obj_binder_normalized_fact_key(fact);
        if let Some(fact_id) = self.known_fact_id(&nested_key) {
            return Ok(Some(fact_id));
        }
        if let Fact::ForallFact(forall_fact) = fact {
            let alpha_key = self.alpha_normalized_forall_cache_key(forall_fact)?;
            if let Some(fact_id) = self.known_fact_id(&alpha_key) {
                return Ok(Some(fact_id));
            }
        }
        if let Fact::ExistFact(exist_fact) = fact {
            let alpha_key = self.alpha_normalized_exist_fact_id_key(exist_fact)?;
            if let Some(fact_id) = self.known_fact_id(&alpha_key) {
                return Ok(Some(fact_id));
            }
        }
        Ok(None)
    }

    pub(crate) fn alpha_normalized_exist_fact_id_key(
        &self,
        exist_fact: &ExistFactEnum,
    ) -> Result<String, RuntimeError> {
        Ok(format!(
            "#exist-fact-id:{}:{}",
            exist_fact.keyword_prefix(),
            Runtime::exist_fact_normalized_body_string(self, exist_fact)?
        ))
    }

    pub fn infer_rule_firing_cached(&self, key: &str) -> bool {
        self.iter_environments_from_top()
            .any(|env| env.cache_infer_rule_firing.contains_key(key))
    }

    pub fn store_infer_rule_firing(&mut self, key: String) {
        self.top_level_env().store_infer_rule_firing(key);
    }

    pub fn get_object_equal_to_cart(&self, obj: &Obj) -> Option<Cart> {
        let key = obj.to_string();
        for env in self.object_lookup_environments(obj) {
            if let Some((known_cart_obj, _)) = env.known_objs_equal_to_cart.get(&key) {
                return Some(known_cart_obj.clone());
            }
            if let Some((_, Some(known_cart_obj), _)) = env.known_objs_equal_to_tuple.get(&key) {
                return Some(known_cart_obj.clone());
            }
        }
        None
    }

    pub fn get_obj_equal_to_set_builder(&self, obj: &Obj) -> Option<SetBuilder> {
        let key = obj.to_string();
        for env in self.object_lookup_environments(obj) {
            if let Some((set_builder, _)) = env.known_objs_equal_to_set_builder.get(&key) {
                return Some(set_builder.clone());
            }
        }
        None
    }

    pub fn get_obj_equal_to_tuple(&self, obj: &Obj) -> Option<Tuple> {
        let key = obj.to_string();
        for env in self.object_lookup_environments(obj) {
            if let Some((Some(known_tuple_obj), _, _)) = env.known_objs_equal_to_tuple.get(&key) {
                return Some(known_tuple_obj.clone());
            }
        }
        None
    }

    pub fn get_obj_tuple_cart(&self, obj: &Obj) -> Option<Cart> {
        let key = obj.to_string();
        for env in self.object_lookup_environments(obj) {
            if let Some((_, Some(known_cart_obj), _)) = env.known_objs_equal_to_tuple.get(&key) {
                return Some(known_cart_obj.clone());
            }
        }
        None
    }

    pub fn get_obj_equal_to_finite_seq_list(&self, obj: &Obj) -> Option<FiniteSeqListObj> {
        let key = obj.to_string();
        for env in self.object_lookup_environments(obj) {
            if let Some((known_list, _, _)) = env.known_objs_equal_to_finite_seq_list.get(&key) {
                return Some(known_list.clone());
            }
        }
        None
    }

    pub fn get_finite_seq_set_for_obj_equal_to_seq_list(&self, obj: &Obj) -> Option<FiniteSeqSet> {
        let key = obj.to_string();
        for env in self.object_lookup_environments(obj) {
            if let Some((_, member_of, _)) = env.known_objs_equal_to_finite_seq_list.get(&key) {
                return member_of.clone();
            }
        }
        None
    }

    pub fn get_obj_equal_to_matrix_list(&self, obj: &Obj) -> Option<MatrixListObj> {
        let key = obj.to_string();
        for env in self.object_lookup_environments(obj) {
            if let Some((known_matrix, _, _)) = env.known_objs_equal_to_matrix_list.get(&key) {
                return Some(known_matrix.clone());
            }
        }
        None
    }

    pub fn get_matrix_set_for_obj_equal_to_matrix_list(&self, obj: &Obj) -> Option<MatrixSet> {
        let key = obj.to_string();
        for env in self.object_lookup_environments(obj) {
            if let Some((_, member_of, _)) = env.known_objs_equal_to_matrix_list.get(&key) {
                return member_of.clone();
            }
        }
        None
    }

    pub fn get_matrix_set_for_obj(&self, obj: &Obj) -> Option<MatrixSet> {
        let key = obj.to_string();
        for env in self.object_lookup_environments(obj) {
            if let Some((matrix_set, _)) = env.known_objs_in_matrix_sets.get(&key) {
                return Some(matrix_set.clone());
            }
        }
        None
    }

    pub fn get_object_equal_to_tuple(&self, obj: &Obj) -> Option<Cart> {
        let key = obj.to_string();
        for env in self.object_lookup_environments(obj) {
            if let Some(cart) = env.known_objs_equal_to_tuple.get(&key) {
                return cart.1.clone();
            }
        }
        None
    }

    pub fn get_object_equal_to_normalized_decimal_number(&self, obj: &Obj) -> Option<Number> {
        let key = obj.to_string();
        for env in self.object_lookup_environments(obj) {
            if let Some(KnownObjValue::SimplifiedNumber(number)) = env.known_obj_values.get(&key) {
                return Some(number.clone());
            }
        }
        None
    }

    pub fn get_known_obj_value_as_obj(&self, obj: &Obj) -> Option<Obj> {
        let key = obj.to_string();
        for env in self.object_lookup_environments(obj) {
            if let Some(known_value) = env.known_obj_values.get(&key) {
                return match known_value {
                    KnownObjValue::SimplifiedNumber(number) => Some(number.clone().into()),
                    KnownObjValue::SimplifiedFraction(div) => Some(div.clone().into()),
                };
            }
        }
        None
    }

    pub(crate) fn known_object_definitions_for_objects(
        &self,
        objects: &[&Obj],
    ) -> Vec<KnownObjectDefinition> {
        let mut environments = self.iter_environments_from_top().collect::<Vec<_>>();
        let mut module_names = Vec::new();
        for object in objects {
            for module_name in self.obj_referenced_module_names(object) {
                if !module_names.contains(&module_name) {
                    module_names.push(module_name);
                }
            }
        }
        for module_name in module_names {
            environments.extend(self.imported_module_environments(&module_name));
        }

        let mut seen = HashSet::new();
        let mut definitions = Vec::new();
        for environment in environments {
            for (key, definition) in environment.known_object_definitions.iter() {
                if seen.insert(key.clone()) {
                    definitions.push(definition.clone());
                }
            }
        }
        definitions.sort_by(|left, right| {
            left.equality
                .line_file
                .0
                .cmp(&right.equality.line_file.0)
                .then_with(|| left.defined.to_string().cmp(&right.defined.to_string()))
        });
        definitions
    }

    pub fn get_all_objs_equal_to_given(&self, given: &str) -> Vec<String> {
        let environments = self.iter_environments_from_top().collect::<Vec<_>>();
        Self::get_all_objs_equal_to_given_in_environments(&environments, given)
    }

    pub fn get_all_obj_representatives_equal_to_given(&self, given: &Obj) -> Vec<Obj> {
        let given_key = obj_equality_key(given);
        let mut result = Vec::new();
        let environments = self.iter_environments_from_top().collect::<Vec<_>>();
        Self::extend_obj_representatives_equal_to_given_in_environments(
            &mut result,
            &environments,
            std::slice::from_ref(&given_key),
        );

        for module_name in self.obj_referenced_module_names(given) {
            let lookup_environments = self.imported_module_environments(&module_name);
            Self::extend_obj_representatives_equal_to_given_in_environments(
                &mut result,
                &lookup_environments,
                std::slice::from_ref(&given_key),
            );
        }

        result.retain(|obj| obj_equality_key(obj) != given_key);
        result
    }

    fn extend_obj_representatives_equal_to_given_in_environments(
        result: &mut Vec<Obj>,
        environments: &[&Environment],
        initial_keys: &[String],
    ) {
        let mut keys = initial_keys.to_vec();
        let mut known_keys = keys.iter().cloned().collect::<HashSet<_>>();
        let mut result_keys = result.iter().map(obj_equality_key).collect::<HashSet<_>>();
        let mut scanned_classes = HashSet::new();
        let mut next_index = 0;
        while next_index < keys.len() {
            let current = keys[next_index].clone();
            next_index += 1;
            for (environment_index, environment) in environments.iter().enumerate() {
                let Some((class_id, _, equivalent_objects)) =
                    environment.known_equality.get_with_class_id(&current)
                else {
                    continue;
                };
                if !scanned_classes.insert((environment_index, class_id)) {
                    continue;
                }
                for object in equivalent_objects.iter() {
                    let object_key = obj_equality_key(object);
                    if known_keys.insert(object_key.clone()) {
                        keys.push(object_key.clone());
                    }
                    if result_keys.insert(object_key) {
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
        let mut known_keys = HashSet::new();
        known_keys.insert(given.to_string());
        let mut scanned_classes = HashSet::new();
        let mut next_index = 0;
        let mut found_equality = false;

        while next_index < result.len() {
            let current = result[next_index].clone();
            next_index += 1;
            for (environment_index, environment) in environments.iter().enumerate() {
                let Some((class_id, _, equivalent_objects)) =
                    environment.known_equality.get_with_class_id(&current)
                else {
                    continue;
                };
                found_equality = true;
                if !scanned_classes.insert((environment_index, class_id)) {
                    continue;
                }
                for object in equivalent_objects.iter() {
                    let object_key = object.to_string();
                    if known_keys.insert(object_key.clone()) {
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

    fn object_lookup_environments(&self, obj: &Obj) -> Vec<&Environment> {
        let mut environments = self.iter_environments_from_top().collect::<Vec<_>>();
        for module_name in self.obj_referenced_module_names(obj) {
            environments.extend(self.imported_module_environments(&module_name));
        }
        environments
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

        let remaining = n_params - consumed;
        if layer.len() > remaining {
            for arg in layer.iter().take(remaining) {
                args.push((**arg).clone());
            }
            extra_layers.push(layer[remaining..].to_vec());
            consumed = n_params;
            outer_application_done = true;
            continue;
        }

        for arg in layer.iter() {
            args.push((**arg).clone());
        }
        consumed += layer.len();

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

fn collect_module_name_from_atomic_name(name: &AtomicName, module_names: &mut Vec<String>) {
    if let AtomicName::WithMod(module_name, _) = name {
        push_module_name(module_names, module_name);
    }
}

fn collect_module_names_from_obj(obj: &Obj, module_names: &mut Vec<String>) {
    match obj {
        Obj::Atom(atom) => collect_module_names_from_atom(atom, module_names),
        Obj::ImaginaryUnit(_) | Obj::EulerNumber(_) | Obj::Pi(_) => {}
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
        Obj::Gcd(x) => collect_module_names_from_two(&x.left, &x.right, module_names),
        Obj::Lcm(x) => collect_module_names_from_two(&x.left, &x.right, module_names),
        Obj::Min(x) => collect_module_names_from_two(&x.left, &x.right, module_names),
        Obj::Max(x) => collect_module_names_from_two(&x.left, &x.right, module_names),
        Obj::Exp(x) => collect_module_names_from_obj(&x.arg, module_names),
        Obj::Ln(x) => collect_module_names_from_obj(&x.arg, module_names),
        Obj::Sign(x) => collect_module_names_from_obj(&x.arg, module_names),
        Obj::Factorial(x) => collect_module_names_from_obj(&x.arg, module_names),
        Obj::Pow(x) => collect_module_names_from_two(&x.base, &x.exponent, module_names),
        Obj::RealPart(x) => collect_module_names_from_obj(&x.arg, module_names),
        Obj::ImaginaryPart(x) => collect_module_names_from_obj(&x.arg, module_names),
        Obj::ComplexAbs(x) => collect_module_names_from_obj(&x.arg, module_names),
        Obj::Log(x) => collect_module_names_from_two(&x.base, &x.arg, module_names),
        Obj::Union(x) => collect_module_names_from_two(&x.left, &x.right, module_names),
        Obj::Intersect(x) => collect_module_names_from_two(&x.left, &x.right, module_names),
        Obj::SetMinus(x) => collect_module_names_from_two(&x.left, &x.right, module_names),
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
        Obj::Reduce(x) => {
            for child in [&x.start, &x.end, &x.func, &x.op, &x.seed] {
                collect_module_names_from_obj(child, module_names);
            }
        }
        Obj::FiniteSetReduce(x) => {
            for child in [&x.set, &x.func, &x.op, &x.seed] {
                collect_module_names_from_obj(child, module_names);
            }
        }
        Obj::Abs(x) => collect_module_names_from_obj(&x.arg, module_names),
        Obj::Floor(x) => collect_module_names_from_obj(&x.arg, module_names),
        Obj::Ceil(x) => collect_module_names_from_obj(&x.arg, module_names),
        Obj::Sin(x) => collect_module_names_from_obj(&x.arg, module_names),
        Obj::Cos(x) => collect_module_names_from_obj(&x.arg, module_names),
        Obj::Tan(x) => collect_module_names_from_obj(&x.arg, module_names),
        Obj::Cot(x) => collect_module_names_from_obj(&x.arg, module_names),
        Obj::Sqrt(x) => collect_module_names_from_obj(&x.arg, module_names),
        Obj::BigUnion(x) => collect_module_names_from_obj(&x.left, module_names),
        Obj::BigIntersect(x) => collect_module_names_from_obj(&x.left, module_names),
        Obj::PowerSet(x) => collect_module_names_from_obj(&x.set, module_names),
        Obj::FiniteSetSize(x) => collect_module_names_from_obj(&x.set, module_names),
        Obj::FiniteSetMax(x) => collect_module_names_from_obj(&x.set, module_names),
        Obj::FiniteSetMin(x) => collect_module_names_from_obj(&x.set, module_names),
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
                collect_module_names_from_quantifier_free_fact(fact, module_names);
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
        FnObjHead::MatrixOperator(matrix) => {
            collect_module_names_from_obj(matrix, module_names);
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
        collect_module_names_from_quantifier_free_fact(fact, module_names);
    }
    collect_module_names_from_obj(&body.ret_set, module_names);
}

fn collect_module_names_from_quantifier_free_fact(
    fact: &QuantifierFreeFact,
    module_names: &mut Vec<String>,
) {
    match fact {
        QuantifierFreeFact::AtomicFact(fact) => {
            collect_module_names_from_atomic_fact(fact, module_names);
        }
        QuantifierFreeFact::AndFact(fact) => {
            for atomic_fact in fact.facts.iter() {
                collect_module_names_from_atomic_fact(atomic_fact, module_names);
            }
        }
        QuantifierFreeFact::ChainFact(fact) => {
            for name in fact.prop_names.iter() {
                collect_module_name_from_atomic_name(name, module_names);
            }
            for obj in fact.objs.iter() {
                collect_module_names_from_obj(obj, module_names);
            }
        }
        QuantifierFreeFact::OrFact(fact) => {
            for branch in fact.facts.iter() {
                collect_module_names_from_and_chain_atomic_fact(branch, module_names);
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

fn collect_module_names_from_two(left: &Obj, right: &Obj, module_names: &mut Vec<String>) {
    collect_module_names_from_obj(left, module_names);
    collect_module_names_from_obj(right, module_names);
}
