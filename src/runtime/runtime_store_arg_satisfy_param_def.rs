//! 将「实参满足展开后的形参类型」对应的事实**写入环境**（与 `define_param_binding_for_param_type` 同构，左端为已求值 [`Obj`]）。
//!
//! 典型顺序：先 `verify_args_satisfy_param_def_flat_types`，再 `store_args_satisfy_param_def`。

use crate::prelude::*;

impl Runtime {
    /// 将形参类型事实落库：与 [`define_param_binding_for_param_type`](crate::execute::exec_def_stmt::Runtime::define_param_binding_for_param_type) 同构，但左端为任意已求值实参 [`Obj`]。
    pub fn store_args_satisfy_param_def(
        &mut self,
        param_defs: &Vec<ParamGroupWithParamType>,
        args: &Vec<Obj>,
        _line_file: LineFile,
    ) -> Result<InferResult, RuntimeError> {
        let instantiated_types =
            self.inst_param_def_with_type_one_by_one(param_defs, args)?;
        let flat_types = ParamGroupWithParamType::flat_instantiated_types_for_args(
            param_defs,
            &instantiated_types,
        );
        let mut infer_result = InferResult::new();
        for (arg, param_type) in args.iter().zip(flat_types.iter()) {
            let ir = self.define_param_binding_for_param_type_on_obj(arg.clone(), param_type)?;
            infer_result.new_infer_result_inside(ir);
        }
        Ok(infer_result)
    }
}
