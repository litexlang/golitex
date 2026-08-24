use crate::prelude::*;
use std::collections::HashMap;

impl Runtime {
    pub fn is_name_used_for_identifier(&self, name: &str) -> bool {
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

    pub fn is_name_used_for_algo(&self, name: &str) -> bool {
        return self.get_algo_definition_by_name(name).is_some();
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

    pub fn store_known_set_builder_obj(
        &mut self,
        name: &str,
        set_builder: SetBuilder,
        line_file: LineFile,
    ) {
        self.top_level_env()
            .known_objs_equal_to_set_builder
            .insert(name.to_string(), (set_builder, line_file));
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

    pub fn store_obj_in_matrix_set(
        &mut self,
        obj: &Obj,
        matrix_set: MatrixSet,
        line_file: LineFile,
    ) {
        self.top_level_env()
            .known_objs_in_matrix_sets
            .insert(obj.to_string(), (matrix_set, line_file));
    }

    pub fn matrix_set_to_fn_set(&self, ms: &MatrixSet, line_file: LineFile) -> FnSet {
        let pair = self.generate_random_unused_names(2);
        let parameters = self
            .fresh_param_group_with_set(pair, StandardSet::NPos.into())
            .expect("internal binder identity counter exhausted");
        FnSet::new(
            vec![parameters.clone()],
            vec![
                AtomicFact::from(LessEqualFact::new(
                    obj_for_bound_param_in_scope(&parameters.params[0], ParamObjType::FnSet),
                    (*ms.row_len).clone(),
                    line_file.clone(),
                ))
                .into(),
                AtomicFact::from(LessEqualFact::new(
                    obj_for_bound_param_in_scope(&parameters.params[1], ParamObjType::FnSet),
                    (*ms.col_len).clone(),
                    line_file.clone(),
                ))
                .into(),
            ],
            (*ms.set).clone(),
        )
        .expect("generated matrix fn set uses fresh parameters")
    }

    pub fn finite_seq_set_to_fn_set(&self, fs: &FiniteSeqSet, line_file: LineFile) -> FnSet {
        let param = self.generate_random_unused_name();
        let param_group = self
            .fresh_param_group_with_set(vec![param], StandardSet::NPos.into())
            .expect("internal binder identity counter exhausted");
        FnSet::new(
            vec![param_group.clone()],
            vec![AtomicFact::from(LessEqualFact::new(
                obj_for_bound_param_in_scope(&param_group.params[0], ParamObjType::FnSet),
                (*fs.n).clone(),
                line_file,
            ))
            .into()],
            (*fs.set).clone(),
        )
        .expect("generated finite sequence fn set uses a fresh parameter")
    }

    pub fn seq_set_to_fn_set(&self, ss: &SeqSet, _line_file: LineFile) -> FnSet {
        let param = self.generate_random_unused_name();
        FnSet::new(
            vec![self
                .fresh_param_group_with_set(vec![param], StandardSet::NPos.into())
                .expect("internal binder identity counter exhausted")],
            vec![],
            (*ss.set).clone(),
        )
        .expect("generated sequence fn set uses a fresh parameter")
    }

    pub fn finite_seq_set_to_fn_set_from_surface_dom_param(
        &self,
        fs: &FiniteSeqSet,
        line_file: LineFile,
        surface_dom_param: &str,
    ) -> Result<FnSet, RuntimeError> {
        let params = vec![self.fresh_param_group_with_set(
            vec![surface_dom_param.to_string()],
            StandardSet::NPos.into(),
        )?];
        let dom_facts: Vec<QuantifierFreeFact> = vec![QuantifierFreeFact::AtomicFact(
            LessEqualFact::new(
                obj_for_bound_param_in_scope(&params[0].params[0], ParamObjType::FnSet),
                (*fs.n).clone(),
                line_file,
            )
            .into(),
        )];
        self.new_fn_set(params, dom_facts, (*fs.set).clone())
    }

    pub fn store_well_defined_obj_cache(&mut self, obj: &Obj) {
        self.top_level_env().cache_well_defined_obj.insert(
            WellDefinedCacheKey::without_function_contract(obj.to_string()),
            CachedWellDefinedObj::ordinary(),
        );
    }

    /// Replays only the sound side effects produced while checking a theorem
    /// or claim conclusion for well-definedness. The certificate excludes the
    /// conclusion itself and every temporary assumption used by the preflight.
    pub fn install_prechecked_well_definedness_certificate(
        &mut self,
        certificate: &Environment,
    ) -> Result<(), RuntimeError> {
        self.top_level_env()
            .merge_committed_child(certificate.clone())
    }
}

impl Runtime {
    pub fn new_fn_set(
        &self,
        params_and_their_sets: impl Into<ParamDefWithSet>,
        dom_facts: Vec<QuantifierFreeFact>,
        ret_set: Obj,
    ) -> Result<FnSet, RuntimeError> {
        let empty: HashMap<String, Obj> = HashMap::new();
        let mut dom_stored = Vec::with_capacity(dom_facts.len());
        for d in &dom_facts {
            dom_stored.push(self.inst_quantifier_free_fact(
                d,
                &empty,
                ParamObjType::FnSet,
                None,
            )?);
        }
        let ret_stored = self.inst_obj(&ret_set, &empty, ParamObjType::FnSet)?;
        Ok(FnSet::new(params_and_their_sets, dom_stored, ret_stored)?)
    }

    pub fn new_anonymous_fn(
        &self,
        params_and_their_sets: impl Into<ParamDefWithSet>,
        dom_facts: Vec<QuantifierFreeFact>,
        ret_set: Obj,
        equal_to: Obj,
    ) -> Result<AnonymousFn, RuntimeError> {
        let empty: HashMap<String, Obj> = HashMap::new();
        let mut dom_stored = Vec::with_capacity(dom_facts.len());
        for d in &dom_facts {
            dom_stored.push(self.inst_quantifier_free_fact(
                d,
                &empty,
                ParamObjType::FnSet,
                None,
            )?);
        }
        let ret_stored = self.inst_obj(&ret_set, &empty, ParamObjType::FnSet)?;
        let eq_stored = self.inst_obj(&equal_to, &empty, ParamObjType::FnSet)?;
        Ok(AnonymousFn::new_with_source_occurrence_id(
            params_and_their_sets,
            dom_stored,
            ret_stored,
            eq_stored,
            Some(self.allocate_source_object_occurrence_id()?),
        )?)
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
        let param_bindings = param_defs.collect_param_bindings();
        if param_bindings.len() != args.len() {
            return Err(
                InstantiateRuntimeError(RuntimeErrorStruct::new_with_just_msg(format!(
                    "params_to_arg_map: expected {} argument(s), got {}",
                    param_bindings.len(),
                    args.len()
                )))
                .into(),
            );
        }

        let mut result: HashMap<String, Obj> = HashMap::new();
        for (binding, arg) in param_bindings.iter().zip(args.iter()) {
            insert_symbol_substitution(&mut result, binding, arg.clone());
        }
        Ok(result)
    }
}
