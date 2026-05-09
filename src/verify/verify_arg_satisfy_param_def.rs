use crate::prelude::*;

impl Runtime {
    pub fn verify_obj_satisfies_param_type(
        &mut self,
        obj: Obj,
        param_type: &ParamType,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        match param_type {
            ParamType::Obj(set_obj) => {
                if let Obj::StructType(struct_ty) = set_obj {
                    return self.verify_obj_satisfies_struct_param_type(
                        obj,
                        struct_ty,
                        verify_state,
                    );
                }
                let fact = InFact::new(obj, set_obj.clone(), default_line_file()).into();
                self.verify_atomic_fact(&fact, verify_state)
            }
            ParamType::Set(_) => {
                let fact = IsSetFact::new(obj, default_line_file()).into();
                self.verify_atomic_fact(&fact, verify_state)
            }
            ParamType::NonemptySet(_) => {
                let fact = IsNonemptySetFact::new(obj, default_line_file()).into();
                self.verify_atomic_fact(&fact, verify_state)
            }
            ParamType::FiniteSet(_) => {
                let fact = IsFiniteSetFact::new(obj, default_line_file()).into();
                self.verify_atomic_fact(&fact, verify_state)
            }
            ParamType::Struct(struct_ty) => {
                self.verify_obj_satisfies_struct_param_type(obj, struct_ty, verify_state)
            }
        }
    }

    pub fn verify_obj_satisfies_struct_param_type(
        &mut self,
        obj: Obj,
        struct_ty: &StructAsParamType,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        if let Obj::StructInstance(instance) = &obj {
            if instance.name.struct_name() != struct_ty.struct_name() {
                return Ok(StmtUnknown::new().into());
            }
            if instance.name.args.len() != struct_ty.args.len() {
                return Ok(StmtUnknown::new().into());
            }
            for (given_arg, expected_arg) in instance.name.args.iter().zip(struct_ty.args.iter()) {
                if given_arg.to_string() != expected_arg.to_string() {
                    return Ok(StmtUnknown::new().into());
                }
            }
            self.verify_obj_well_defined_and_store_cache(&obj, verify_state)?;
            return Ok(NonFactualStmtSuccess::new_with_stmt(
                DoNothingStmt::new(default_line_file()).into(),
            )
            .into());
        }
        let Some(arg_name) = obj_name_for_struct_param_check(&obj) else {
            return Ok(StmtUnknown::new().into());
        };
        let struct_name = struct_ty.struct_name();
        for env in self.iter_environments_from_top() {
            if let Some(known_struct_name) = env.known_name_belong_to_struct.get(&arg_name) {
                if known_struct_name == &struct_name {
                    return Ok(NonFactualStmtSuccess::new_with_stmt(
                        DoNothingStmt::new(default_line_file()).into(),
                    )
                    .into());
                }
                return Ok(StmtUnknown::new().into());
            }
        }
        Ok(StmtUnknown::new().into())
    }

    pub fn verify_args_satisfy_param_def_flat_types(
        &mut self,
        param_defs: &ParamDefWithType,
        args: &Vec<Obj>,
        verify_state: &VerifyState,
        to_inst_param_type: ParamObjType,
    ) -> Result<StmtResult, RuntimeError> {
        let instantiated_types =
            self.inst_param_def_with_type_one_by_one(param_defs, args, to_inst_param_type)?;
        let flat_types = param_defs.flat_instantiated_types_for_args(&instantiated_types);
        let mut infer_result = InferResult::new();
        for (arg, param_type) in args.iter().zip(flat_types.iter()) {
            let verify_result =
                self.verify_obj_satisfies_param_type(arg.clone(), param_type, verify_state)?;
            if verify_result.is_unknown() {
                return Ok(verify_result);
            }
            match verify_result {
                StmtResult::NonFactualStmtSuccess(x) => {
                    infer_result.new_infer_result_inside(x.infers);
                }
                StmtResult::FactualStmtSuccess(x) => {
                    infer_result.new_infer_result_inside(x.infers);
                }
                StmtResult::StmtUnknown(_) => unreachable!(),
            }
        }
        Ok(NonFactualStmtSuccess::new(
            DoNothingStmt::new(default_line_file()).into(),
            infer_result,
            Vec::new(),
        )
        .into())
    }
}

fn obj_name_for_struct_param_check(obj: &Obj) -> Option<String> {
    match obj {
        Obj::Atom(AtomObj::Identifier(identifier)) => Some(identifier.name.clone()),
        Obj::Atom(AtomObj::Forall(p)) => Some(p.name.clone()),
        Obj::Atom(AtomObj::Def(p)) => Some(p.name.clone()),
        Obj::Atom(AtomObj::Exist(p)) => Some(p.name.clone()),
        Obj::Atom(AtomObj::SetBuilder(p)) => Some(p.name.clone()),
        Obj::Atom(AtomObj::FnSet(p)) => Some(p.name.clone()),
        Obj::Atom(AtomObj::Induc(p)) => Some(p.name.clone()),
        Obj::Atom(AtomObj::DefAlgo(p)) => Some(p.name.clone()),
        Obj::Atom(AtomObj::DefStructField(p)) => Some(p.name.clone()),
        _ => None,
    }
}
