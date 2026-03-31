use crate::prelude::*;

impl Runtime {
    pub fn verify_restrict_fact_using_its_definition(
        &mut self,
        restrict_fact: &RestrictFact,
        verify_state: &VerifyState,
    ) -> Result<Option<NonErrStmtExecResult>, VerifyError> {
        let function = &restrict_fact.obj;

        // get function set of function
        let function_set = self.get_cloned_fn_set_where_fn_belongs_to(function);

        match function_set {
            Some(fn_set) => match fn_set {
                FnSetObj::FnSetWithDom(fn_set_with_dom) => {
                    return self.verify_restrict_fact_with_fn_set_with_dom(
                        restrict_fact,
                        &fn_set_with_dom,
                        verify_state,
                    );
                }
                FnSetObj::FnSetWithoutParams(fn_set_without_dom) => {
                    return self.verify_restrict_fact_with_fn_set_without_dom(
                        restrict_fact,
                        &fn_set_without_dom,
                        verify_state,
                    );
                }
            },
            None => {
                return Err(VerifyError::new(
                    Fact::AtomicFact(AtomicFact::RestrictFact(restrict_fact.clone())),
                    String::new(),
                    restrict_fact.line_file,
                    Some(RuntimeError::WellDefinedError(WellDefinedError::new(
                        format!(
                            "function `{}` belongs to what function set is unknown",
                            function.to_string()
                        ),
                        None,
                        DEFAULT_LINE_FILE.clone(),
                    ))),
                ));
            }
        }
    }

    fn verify_restrict_fact_with_fn_set_with_dom(
        &mut self,
        _restrict_fact: &RestrictFact,
        _fn_set_with_dom: &FnSetWithParams,
        _verify_state: &VerifyState,
    ) -> Result<Option<NonErrStmtExecResult>, VerifyError> {
        unimplemented!();
    }

    fn verify_restrict_fact_with_fn_set_without_dom(
        &mut self,
        restrict_fact: &RestrictFact,
        fn_set_without_dom: &FnSetWithoutParams,
        verify_state: &VerifyState,
    ) -> Result<Option<NonErrStmtExecResult>, VerifyError> {
        unimplemented!();
    }
}
