use crate::prelude::*;

impl Runtime {
    pub fn store_args_satisfy_param_type_when_not_defining_new_identifiers(
        &mut self,
        param_defs: &Vec<ParamGroupWithParamType>,
        args: &Vec<Obj>,
        _line_file: LineFile,
    ) -> Result<InferResult, RuntimeError> {
        let instantiated_types = self.inst_param_def_with_type_one_by_one(param_defs, args)?;

        let mut infer_result = InferResult::new();
        for (arg, param_type) in args.iter().zip(instantiated_types.iter()) {
            let new_fact: Fact = match param_type {
                ParamType::Set(_) => Fact::AtomicFact(AtomicFact::IsSetFact(IsSetFact::new(
                    arg.clone(),
                    _line_file.clone(),
                ))),
                ParamType::NonemptySet(_) => Fact::AtomicFact(AtomicFact::IsNonemptySetFact(
                    IsNonemptySetFact::new(arg.clone(), _line_file.clone()),
                )),
                ParamType::FiniteSet(_) => Fact::AtomicFact(AtomicFact::IsFiniteSetFact(
                    IsFiniteSetFact::new(arg.clone(), _line_file.clone()),
                )),
                ParamType::Obj(obj) => Fact::AtomicFact(AtomicFact::InFact(InFact::new(
                    arg.clone(),
                    obj.clone(),
                    _line_file.clone(),
                ))),
                ParamType::Struct(struct_ty) => Fact::AtomicFact(AtomicFact::InFact(InFact::new(
                    arg.clone(),
                    Obj::StructObj(struct_ty.clone()),
                    _line_file.clone(),
                ))),
            };
            infer_result.new_infer_result_inside(
                self.store_fact_without_well_defined_verified_and_infer(new_fact)?,
            );
        }

        Ok(infer_result)
    }
}
