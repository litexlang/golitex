use crate::prelude::*;

impl Runtime {
    pub fn store_args_satisfy_param_type_when_not_defining_new_identifiers(
        &mut self,
        param_defs: &ParamDefWithType,
        args: &Vec<Obj>,
        _line_file: LineFile,
    ) -> Result<InferResult, RuntimeError> {
        let instantiated_types = self.inst_param_def_with_type_one_by_one(param_defs, args)?;

        let mut infer_result = InferResult::new();
        for (arg, param_type) in args.iter().zip(instantiated_types.iter()) {
            let new_fact: Fact = match param_type {
                ParamType::Set(_) => IsSetFact::new(arg.clone(), _line_file.clone()).into(),
                ParamType::NonemptySet(_) => {
                    IsNonemptySetFact::new(arg.clone(), _line_file.clone()).into()
                }
                ParamType::FiniteSet(_) => {
                    IsFiniteSetFact::new(arg.clone(), _line_file.clone()).into()
                }
                ParamType::Obj(obj) => {
                    InFact::new(arg.clone(), obj.clone(), _line_file.clone()).into()
                }
                ParamType::Struct(struct_ty) => InFact::new(
                    arg.clone(),
                    Obj::StructObj(struct_ty.clone()),
                    _line_file.clone(),
                )
                .into(),
            };
            infer_result.new_infer_result_inside(
                self.store_fact_without_well_defined_verified_and_infer(new_fact)?,
            );
        }

        Ok(infer_result)
    }
}
