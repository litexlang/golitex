use crate::prelude::*;
use crate::verify::verify_equality_by_builtin_rules::objs_equal_by_display_string;
use std::result::Result;

/// Two atomic facts of the form `s > t` / `s <= t` (or `<` / `>=`) with the same left and right
/// operands; the disjunction is a trivial order split (totally ordered carriers such as `R`).
fn order_split_or_is_exhaustive_pair(a: &AtomicFact, b: &AtomicFact) -> bool {
    use AtomicFact::*;
    match (a, b) {
        (GreaterFact(g), LessEqualFact(le)) => {
            objs_equal_by_display_string(&g.left, &le.left)
                && objs_equal_by_display_string(&g.right, &le.right)
        }
        (LessFact(l), GreaterEqualFact(ge)) => {
            objs_equal_by_display_string(&l.left, &ge.left)
                && objs_equal_by_display_string(&l.right, &ge.right)
        }
        (LessEqualFact(le), GreaterFact(g)) => {
            objs_equal_by_display_string(&le.left, &g.left)
                && objs_equal_by_display_string(&le.right, &g.right)
        }
        (GreaterEqualFact(ge), LessFact(l)) => {
            objs_equal_by_display_string(&ge.left, &l.left)
                && objs_equal_by_display_string(&ge.right, &l.right)
        }
        _ => false,
    }
}

fn obj_is_literal_neg_one_for_abs_or_builtin(obj: &Obj) -> bool {
    match obj {
        Obj::Number(n) => n.normalized_value == "-1",
        _ => false,
    }
}

fn obj_is_negation_of_for_abs_or_builtin(obj: &Obj, expected_arg: &Obj) -> bool {
    match obj {
        Obj::Mul(m) => {
            (obj_is_literal_neg_one_for_abs_or_builtin(m.left.as_ref())
                && objs_equal_by_display_string(m.right.as_ref(), expected_arg))
                || (obj_is_literal_neg_one_for_abs_or_builtin(m.right.as_ref())
                    && objs_equal_by_display_string(m.left.as_ref(), expected_arg))
        }
        _ => false,
    }
}

fn abs_sign_split_or_is_exhaustive_pair(a: &AtomicFact, b: &AtomicFact) -> bool {
    let (AtomicFact::EqualFact(first), AtomicFact::EqualFact(second)) = (a, b) else {
        return false;
    };
    let (arg, first_other) = match (&first.left, &first.right) {
        (Obj::Abs(abs), other) => (abs.arg.as_ref(), other),
        (other, Obj::Abs(abs)) => (abs.arg.as_ref(), other),
        _ => return false,
    };
    if !objs_equal_by_display_string(arg, first_other) {
        return false;
    }
    let (second_arg, second_other) = match (&second.left, &second.right) {
        (Obj::Abs(abs), other) => (abs.arg.as_ref(), other),
        (other, Obj::Abs(abs)) => (abs.arg.as_ref(), other),
        _ => return false,
    };
    objs_equal_by_display_string(arg, second_arg)
        && obj_is_negation_of_for_abs_or_builtin(second_other, arg)
}

impl Runtime {
    pub fn verify_or_fact(
        &mut self,
        or_fact: &OrFact,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        if let Some(cached_result) =
            self.verify_fact_from_cache_using_display_string(&or_fact.clone().into())
        {
            return Ok(cached_result);
        }

        if !verify_state.well_defined_already_verified {
            if let Err(e) = self.verify_or_fact_well_defined(or_fact, verify_state) {
                return Err({
                    VerifyRuntimeError(RuntimeErrorStruct::new(
                        Some(Fact::from(or_fact.clone()).into_stmt()),
                        String::new(),
                        or_fact.line_file.clone(),
                        Some(e),
                        vec![],
                    ))
                    .into()
                });
            }
        }

        let verify_state_for_children = verify_state.make_state_with_req_ok_set_to_true();

        if or_fact.facts.len() == 2 {
            if let (
                AndChainAtomicFact::AtomicFact(first_atomic),
                AndChainAtomicFact::AtomicFact(second_atomic),
            ) = (&or_fact.facts[0], &or_fact.facts[1])
            {
                if first_atomic.make_reversed().to_string() == second_atomic.to_string() {
                    return Ok(
                        (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                            or_fact.clone().into(),
                            "or: complementary atomic facts (make_reversed first equals second)"
                                .to_string(),
                            Vec::new(),
                        ))
                        .into(),
                    );
                }
                if order_split_or_is_exhaustive_pair(first_atomic, second_atomic)
                    || order_split_or_is_exhaustive_pair(second_atomic, first_atomic)
                {
                    return Ok(
                        (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                            or_fact.clone().into(),
                            "or: complementary order relations (strict vs non-strict) on the same terms"
                                .to_string(),
                            Vec::new(),
                        ))
                        .into(),
                    );
                }
                if abs_sign_split_or_is_exhaustive_pair(first_atomic, second_atomic)
                    || abs_sign_split_or_is_exhaustive_pair(second_atomic, first_atomic)
                {
                    return Ok(
                        (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                            or_fact.clone().into(),
                            "or: abs(x) is x or -x".to_string(),
                            Vec::new(),
                        ))
                        .into(),
                    );
                }
            }
        }

        for fact in or_fact.facts.iter() {
            let result = self.verify_and_chain_atomic_fact(fact, &verify_state_for_children)?;
            if result.is_true() {
                return Ok(
                    (FactualStmtSuccess::new_with_verified_by_known_fact(
                        or_fact.clone().into(),
                        VerifiedByResult::wrap_bys(vec![VerifiedByResult::Fact(
                            fact.clone().into(),
                            fact.to_string(),
                        )]),
                        Vec::new(),
                    ))
                    .into(),
                );
            }
        }

        let result = self.verify_or_fact_with_known_or_facts(or_fact)?;
        if result.is_true() {
            return Ok(result);
        }

        let result = self.verify_or_fact_with_known_forall(or_fact, verify_state)?;
        if result.is_true() {
            return Ok(result);
        }

        Ok((StmtUnknown::new()).into())
    }

    pub fn verify_or_fact_with_known_or_facts(
        &mut self,
        or_fact: &OrFact,
    ) -> Result<StmtResult, RuntimeError> {
        let args_in_or_fact = or_fact.get_args_from_fact();
        let mut all_objs_equal_to_each_arg: Vec<Vec<String>> = Vec::new();
        for arg in args_in_or_fact.iter() {
            let mut all_objs_equal_to_current_arg =
                self.get_all_objs_equal_to_given(&arg.to_string());
            if all_objs_equal_to_current_arg.is_empty() {
                all_objs_equal_to_current_arg.push(arg.to_string());
            }
            all_objs_equal_to_each_arg.push(all_objs_equal_to_current_arg);
        }

        for environment in self.iter_environments_from_top() {
            let result = Self::verify_or_fact_with_known_or_facts_with_facts_in_environment(
                environment,
                or_fact,
                &all_objs_equal_to_each_arg,
            )?;
            if result.is_true() {
                return Ok(result);
            }
        }

        Ok((StmtUnknown::new()).into())
    }

    pub fn verify_or_fact_with_known_or_facts_with_facts_in_environment(
        environment: &Environment,
        or_fact: &OrFact,
        all_objs_equal_to_each_arg: &Vec<Vec<String>>,
    ) -> Result<StmtResult, RuntimeError> {
        if let Some(known_or_facts) = environment.known_or_facts.get(&or_fact.key()) {
            for known_or_fact in known_or_facts.iter() {
                let result = Self::_verify_or_fact_the_same_type_and_return_matched_args(
                    known_or_fact,
                    or_fact,
                )?;
                let mut all_args_match = true;
                if let Some(matched_args) = result {
                    for (index, matched_arg) in matched_args.iter().enumerate() {
                        let known_arg_string = matched_arg.0.to_string();

                        if known_arg_string != matched_arg.1.to_string()
                            && !all_objs_equal_to_each_arg[index].contains(&known_arg_string)
                        {
                            all_args_match = false;
                            break;
                        }
                    }
                }

                if all_args_match {
                    return Ok((FactualStmtSuccess::new_with_verified_by_known_fact(
                            or_fact.clone().into(),
                            VerifiedByResult::wrap_bys(vec![VerifiedByResult::Fact(
                                known_or_fact.clone().into(),
                                known_or_fact.to_string(),
                            )]),
                            Vec::new(),
                        ))
                        .into());
                }
            }
        }

        return Ok((StmtUnknown::new()).into());
    }
}
