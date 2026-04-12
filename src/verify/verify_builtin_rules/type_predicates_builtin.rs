use crate::prelude::*;

impl Runtime {
    pub(crate) fn _verify_is_nonempty_set_fact_with_builtin_rules(
        &mut self,
        is_nonempty_set_fact: &IsNonemptySetFact,
        _verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        match &is_nonempty_set_fact.set {
            Obj::StandardSet(_) => Ok((FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    Fact::AtomicFact(AtomicFact::IsNonemptySetFact(is_nonempty_set_fact.clone())),
                    "standard_nonempty_set".to_string(),
                    Vec::new(),
                )).into()),
            Obj::ListSet(list_set) => {
                if list_set.list.is_empty() {
                    Ok((StmtUnknown::new()).into())
                } else {
                    Ok((FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                            Fact::AtomicFact(AtomicFact::IsNonemptySetFact(
                                is_nonempty_set_fact.clone(),
                            )),
                            "list_set_nonempty_has_member_in_syntax".to_string(),
                            Vec::new(),
                        )).into())
                }
            }
            Obj::Cart(cart) => {
                for arg_obj in &cart.args {
                    let is_nonempty_set_result = self
                        .verify_non_equational_atomic_fact_with_builtin_rules(
                            &IsNonemptySetFact::new(
                                *arg_obj.clone(),
                                is_nonempty_set_fact.line_file.clone(),
                            ).into(),
                            _verify_state,
                        )?;

                    if is_nonempty_set_result.is_unknown() {
                        return Ok((StmtUnknown::new()).into());
                    }
                }

                Ok((FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        Fact::AtomicFact(AtomicFact::IsNonemptySetFact(
                            is_nonempty_set_fact.clone(),
                        )),
                        format!(
                            "sets `{}` in `{}` are nonempty sets",
                            cart.args
                                .iter()
                                .map(|arg| arg.as_ref().to_string())
                                .collect::<Vec<String>>()
                                .join(", "),
                            cart.to_string()
                        ),
                        Vec::new(),
                    )).into())
            }
            Obj::FnSet(fn_set) => {
                let ret_nonempty_fact = IsNonemptySetFact::new(
                    fn_set.ret_set.as_ref().clone(),
                    is_nonempty_set_fact.line_file.clone(),
                ).into();
                let ret_check = self.verify_non_equational_atomic_fact_with_builtin_rules(
                    &ret_nonempty_fact,
                    _verify_state,
                )?;
                if ret_check.is_true() {
                    Ok((FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                            Fact::AtomicFact(AtomicFact::IsNonemptySetFact(
                                is_nonempty_set_fact.clone(),
                            )),
                            "fn_set_is_nonempty_when_ret_set_is_nonempty".to_string(),
                            Vec::new(),
                        )).into())
                } else {
                    Ok((StmtUnknown::new()).into())
                }
            }
            _ => Ok((StmtUnknown::new()).into()),
        }
    }

    pub(crate) fn _verify_is_finite_set_fact_with_builtin_rules(
        &mut self,
        is_finite_set_fact: &IsFiniteSetFact,
        _verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        match &is_finite_set_fact.set {
            Obj::ListSet(_) => Ok((FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    Fact::AtomicFact(AtomicFact::IsFiniteSetFact(is_finite_set_fact.clone())),
                    "list_set_finite".to_string(),
                    Vec::new(),
                )).into()),
            _ => Ok((StmtUnknown::new()).into()),
        }
    }

    pub(crate) fn _verify_is_cart_fact_with_builtin_rules(
        &mut self,
        is_cart_fact: &IsCartFact,
        _verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        match &is_cart_fact.set {
            Obj::Cart(_) => {
                return Ok((FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        Fact::AtomicFact(AtomicFact::IsCartFact(is_cart_fact.clone())),
                        "any `cart` object is a cart".to_string(),
                        Vec::new(),
                    )).into());
            }
            _ => Ok((StmtUnknown::new()).into()),
        }
    }

    pub(crate) fn _verify_is_tuple_fact_with_builtin_rules(
        &mut self,
        is_tuple_fact: &IsTupleFact,
        _verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        match &is_tuple_fact.set {
            Obj::Tuple(t) => {
                if t.args.len() < 2 {
                    return Ok((StmtUnknown::new()).into());
                }
                return Ok((FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        Fact::AtomicFact(AtomicFact::IsTupleFact(is_tuple_fact.clone())),
                        "any `cart_dim` object is a cart_dim".to_string(),
                        Vec::new(),
                    )).into());
            }
            _ => {
                if let Some((_, _, _)) = self
                    .top_level_env()
                    .known_objs_equal_to_tuple
                    .get(&is_tuple_fact.set.to_string())
                {
                    return Ok((FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                            Fact::AtomicFact(AtomicFact::IsTupleFact(is_tuple_fact.clone())),
                            "it is a known tuple".to_string(),
                            Vec::new(),
                        )).into());
                }

                Ok((StmtUnknown::new()).into())
            }
        }
    }

    pub(crate) fn _verify_not_is_nonempty_set_fact_with_builtin_rules(
        &mut self,
        not_is_nonempty_set_fact: &NotIsNonemptySetFact,
        _verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        if let Obj::ListSet(list_set) = &not_is_nonempty_set_fact.set {
            if list_set.list.is_empty() {
                return Ok((FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        Fact::AtomicFact(AtomicFact::NotIsNonemptySetFact(
                            not_is_nonempty_set_fact.clone(),
                        )),
                        "list_set_empty".to_string(),
                        Vec::new(),
                    )).into());
            }
        }
        Ok((StmtUnknown::new()).into())
    }
}
