use crate::prelude::*;
use crate::verify::verify_equality_by_builtin_rules::factual_equal_success_by_builtin_reason;

impl Runtime {
    // Beta-reduction for anonymous `fn` heads: if argument lists match the parameter list, substitute
    // into the braced `equal_to` body and require that to equal the other side (same as evaluation).
    pub(crate) fn try_verify_anonymous_fn_application_equals_other_side(
        &mut self,
        statement_left: &Obj,
        statement_right: &Obj,
        application_side: &Obj,
        other_side: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let Obj::FnObj(fn_obj) = application_side else {
            return Ok(None);
        };
        let FnObjHead::AnonymousFnLiteral(af) = fn_obj.head.as_ref() else {
            return Ok(None);
        };
        if fn_obj.body.is_empty() {
            return Ok(None);
        }
        let param_defs = &af.body.params_def_with_set;
        let n_params = ParamGroupWithSet::number_of_params(param_defs);
        if n_params == 0 {
            return Ok(None);
        }
        let mut args: Vec<Obj> = Vec::new();
        for g in fn_obj.body.iter() {
            for b in g.iter() {
                args.push((**b).clone());
            }
        }
        if args.len() != n_params {
            return Ok(None);
        }
        let param_to_arg_map =
            ParamGroupWithSet::param_defs_and_args_to_param_to_arg_map(param_defs, &args);
        let reduced =
            self.inst_obj(af.equal_to.as_ref(), &param_to_arg_map, ParamObjType::FnSet)?;
        let inner =
            self.verify_objs_are_equal(&reduced, other_side, line_file.clone(), verify_state)?;
        if inner.is_true() {
            return Ok(Some(factual_equal_success_by_builtin_reason(
                statement_left,
                statement_right,
                line_file,
                "equality: anonymous function application — substitute args into the body, equals the other side",
            )));
        }
        Ok(None)
    }
}
