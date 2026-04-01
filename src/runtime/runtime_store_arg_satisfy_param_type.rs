use crate::prelude::*;

impl Runtime {
    pub fn store_arg_satisfy_param_type(
        &mut self,
        arg: &Obj,
        param_type: &ParamType,
        line_file: (usize, usize),
    ) -> Result<InferResult, RuntimeErrorStruct> {
        match param_type {
            ParamType::Obj(obj) => {
                let in_fact = Fact::AtomicFact(AtomicFact::InFact(InFact::new(
                    arg.clone(),
                    obj.clone(),
                    line_file.clone(),
                )));
                self.store_fact_without_well_defined_verified_and_infer(in_fact)
            }
            ParamType::Set(_) => {
                let is_set_fact = Fact::AtomicFact(AtomicFact::IsSetFact(IsSetFact::new(
                    arg.clone(),
                    line_file,
                )));
                self.store_fact_without_well_defined_verified_and_infer(is_set_fact)
            }
            ParamType::NonemptySet(_) => {
                let is_nonempty_set_fact = Fact::AtomicFact(AtomicFact::IsNonemptySetFact(IsNonemptySetFact::new(
                    arg.clone(),
                    line_file,
                )));
                self.store_fact_without_well_defined_verified_and_infer(is_nonempty_set_fact)
            }
            ParamType::FiniteSet(_) => {
                let is_finite_set_fact = Fact::AtomicFact(AtomicFact::IsFiniteSetFact(IsFiniteSetFact::new(
                    arg.clone(),
                    line_file,
                )));
                self.store_fact_without_well_defined_verified_and_infer(is_finite_set_fact)
            }
            ParamType::Family(family) => {
                self._store_arg_satisfy_param_type_family(arg, family, line_file)
            }
            ParamType::Struct(struct_ty) => {
                self._store_arg_satisfy_param_type_struct(arg, struct_ty, line_file)
            }
        }
    }

    /// 先 [`ParamDefWithParamType::instantiate_param_def_with_type_one_by_one`] 再展开为每个形参对应的
    /// [`ParamType`]，对每个 `(arg, param_type)` 调用 [`Self::store_arg_satisfy_param_type`]，合并 [`InferResult`]。
    pub fn store_args_satisfy_param_def(
        &mut self,
        param_defs: &Vec<ParamDefWithParamType>,
        args: &Vec<Obj>,
        line_file: (usize, usize),
    ) -> Result<InferResult, RuntimeError> {
        let instantiated_types =
            ParamDefWithParamType::instantiate_param_def_with_type_one_by_one(param_defs, args)?;
        let flat_types = ParamDefWithParamType::flat_instantiated_types_for_args(
            param_defs,
            &instantiated_types,
        );
        let mut infer_result = InferResult::new();
        for (arg, param_type) in args.iter().zip(flat_types.iter()) {
            let ir = self
                .store_arg_satisfy_param_type(arg, param_type, line_file)
                .map_err(RuntimeError::from)?;
            infer_result.new_infer_result_inside(ir);
        }
        Ok(infer_result)
    }

    fn _store_arg_satisfy_param_type_family(
        &mut self,
        _arg: &Obj,
        _family: &FamilyParamType,
        _line_file: (usize, usize),
    ) -> Result<InferResult, RuntimeErrorStruct> {
        Ok(InferResult::new())
    }

    fn _store_arg_satisfy_param_type_struct(
        &mut self,
        _arg: &Obj,
        _struct_ty: &StructParamType,
        _line_file: (usize, usize),
    ) -> Result<InferResult, RuntimeErrorStruct> {
        Ok(InferResult::new())
    }
}