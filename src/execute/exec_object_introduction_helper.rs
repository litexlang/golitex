use crate::prelude::*;

impl Runtime {
    pub fn object_introduction_nonempty_checks_for_param_def(
        &mut self,
        param_defs: &ParamDefWithType,
    ) -> Result<Vec<StmtResult>, RuntimeError> {
        let mut checks = Vec::new();
        for param_def in param_defs.groups.iter() {
            if let Some(fact) = nonempty_check_fact_for_param_type(&param_def.param_type) {
                let verify_state = VerifyState::new(0, false);
                let result = self.verify_fact_return_err_if_not_true(&fact, &verify_state)?;
                checks.push(result);
            }
        }
        Ok(checks)
    }

    pub fn object_introduction_items_for_defined_params(
        &self,
        param_defs: &ParamDefWithType,
        line_file: LineFile,
        binding_kind: ParamObjType,
    ) -> Vec<ObjectIntroductionItem> {
        let mut items = Vec::new();
        for (name, param_type) in param_defs.collect_param_names_with_types() {
            let obj = param_binding_element_obj_for_store(name.clone(), binding_kind);
            let fact = self.object_introduction_fact_for_param_type(
                obj,
                &param_type,
                line_file.clone(),
                true,
            );
            items.push(ObjectIntroductionItem::new(name, vec![fact]));
        }
        items
    }

    pub fn object_introduction_items_for_named_args(
        &self,
        param_defs: &ParamDefWithType,
        names: &[String],
        args: &Vec<Obj>,
        line_file: LineFile,
        param_obj_type: ParamObjType,
    ) -> Result<Vec<ObjectIntroductionItem>, RuntimeError> {
        let instantiated_types =
            self.inst_param_def_with_type_one_by_one(param_defs, args, param_obj_type)?;
        let mut items = Vec::new();
        for ((name, arg), param_type) in
            names.iter().zip(args.iter()).zip(instantiated_types.iter())
        {
            let fact = self.object_introduction_fact_for_param_type(
                arg.clone(),
                param_type,
                line_file.clone(),
                false,
            );
            items.push(ObjectIntroductionItem::new(name.clone(), vec![fact]));
        }
        Ok(items)
    }

    pub fn add_facts_to_object_introduction_items(
        items: &mut Vec<ObjectIntroductionItem>,
        facts: &[Fact],
    ) {
        for item in items.iter_mut() {
            for fact in facts.iter() {
                item.facts.push(fact.clone());
            }
        }
    }

    fn object_introduction_fact_for_param_type(
        &self,
        obj: Obj,
        param_type: &ParamType,
        line_file: LineFile,
        use_defined_param_storage_shape: bool,
    ) -> Fact {
        match param_type {
            ParamType::Set(_) => IsSetFact::new(obj, line_file).into(),
            ParamType::NonemptySet(_) => IsNonemptySetFact::new(obj, line_file).into(),
            ParamType::FiniteSet(_) => IsFiniteSetFact::new(obj, line_file).into(),
            ParamType::Obj(param_obj) => {
                let stored_param_obj = if use_defined_param_storage_shape {
                    self.defined_param_storage_obj_for_param_obj(param_obj, line_file.clone())
                } else {
                    param_obj.clone()
                };
                InFact::new(obj, stored_param_obj, line_file).into()
            }
        }
    }

    fn defined_param_storage_obj_for_param_obj(&self, param_obj: &Obj, line_file: LineFile) -> Obj {
        match param_obj {
            Obj::FiniteSeqSet(fs) => self.finite_seq_set_to_fn_set(fs, line_file).into(),
            Obj::SeqSet(ss) => self.seq_set_to_fn_set(ss, line_file).into(),
            Obj::MatrixSet(ms) => self.matrix_set_to_fn_set(ms, line_file).into(),
            _ => param_obj.clone(),
        }
    }
}

fn nonempty_check_fact_for_param_type(param_type: &ParamType) -> Option<Fact> {
    match param_type {
        ParamType::Set(_) | ParamType::NonemptySet(_) | ParamType::FiniteSet(_) => None,
        ParamType::Obj(param_set) => {
            let nonempty_obj = match param_set {
                Obj::FnSet(fn_set) => fn_set.body.ret_set.as_ref().clone(),
                Obj::AnonymousFn(anon) => anon.body.ret_set.as_ref().clone(),
                _ => param_set.clone(),
            };
            Some(IsNonemptySetFact::new(nonempty_obj, default_line_file()).into())
        }
    }
}
