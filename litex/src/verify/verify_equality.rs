use std::rc::Rc;
use crate::obj::Obj;
use crate::simplify_polynomial::two_objs_equal_by_polynomial_simplification;
use crate::fact::EqualFact;
use crate::execute::Executor;
use crate::result::StmtUnknown;
use crate::error::VerifyError;
use crate::result::NonErrStmtExecResult;
use crate::result::FactVerifiedByBuiltinRules;
use crate::verify::VerifyState;

impl<'a> Executor<'a> {
    pub fn verify_equal_fact(&mut self, equal_fact: &EqualFact, verify_state: &VerifyState) -> Result<NonErrStmtExecResult, VerifyError> {
        let mut result = self.verify_equality_by_builtin_rules(equal_fact)?;
        if result.is_true() {
            return Ok(result);
        }

        result = self.verify_equality_with_known_equalities(equal_fact, verify_state)?;
        if result.is_true() {
            return Ok(result);
        }

        if verify_state.is_round_0() {
            let result = self.verify_equality_with_known_forall_facts(equal_fact, verify_state)?;
            if result.is_true() {
                return Ok(result);
            }
        }
        
        Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()))
    }

    pub fn verify_equality_by_they_are_the_same(left: &Obj, right: &Obj) -> bool {
        if left.to_string() == right.to_string() {
            return true;
        }
        false
    }

    fn verify_equality_by_builtin_rules(&mut self, equal_fact: &EqualFact) -> Result<NonErrStmtExecResult, VerifyError> {
        if Self::verify_equality_by_they_are_the_same(&equal_fact.left, &equal_fact.right) {
            return Ok(NonErrStmtExecResult::FactVerifiedByBuiltinRules(FactVerifiedByBuiltinRules::new(equal_fact.to_string(), "the same".to_string(), equal_fact.line_file_index)));
        }
        
        if equal_fact.left.two_objs_can_be_calculated_and_equal_by_calculation(&equal_fact.right) {
            return Ok(NonErrStmtExecResult::FactVerifiedByBuiltinRules(FactVerifiedByBuiltinRules::new(equal_fact.to_string(), "calculation".to_string(), equal_fact.line_file_index)));
        }

        if two_objs_equal_by_polynomial_simplification(&equal_fact.left, &equal_fact.right) {
            return Ok(NonErrStmtExecResult::FactVerifiedByBuiltinRules(FactVerifiedByBuiltinRules::new(equal_fact.to_string(), "polynomial simplification".to_string(), equal_fact.line_file_index)));
        }

        Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()))
    }

    fn verify_equality_with_known_equalities(&mut self, equal_fact: &EqualFact, _verify_state: &VerifyState) -> Result<NonErrStmtExecResult, VerifyError> {
        let left_string = equal_fact.left.to_string();
        let right_string = equal_fact.right.to_string();

        let known_pairs = self.collect_known_equality_pairs_from_envs(&left_string, &right_string);
        for (known_left, known_right) in known_pairs {
            if let Some(result) = self.try_verify_equality_with_known(equal_fact, known_left.as_ref(), known_right.as_ref())? {
                return Ok(result);
            }
        }
        let known_left = self.runtime_context.builtin_environment.known_equality.get(&left_string).map(Rc::clone);
        let known_right = self.runtime_context.builtin_environment.known_equality.get(&right_string).map(Rc::clone);
        if let Some(result) = self.try_verify_equality_with_known(equal_fact, known_left.as_ref(), known_right.as_ref())? {
            return Ok(result);
        }

        Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()))
    }

    /// Collect (known_left, known_right) from each env in top-to-bottom order (last env first).
    fn collect_known_equality_pairs_from_envs(
        &self,
        left_string: &str,
        right_string: &str,
    ) -> Vec<(Option<Rc<Vec<Obj>>>, Option<Rc<Vec<Obj>>>)> {
        let mut pairs = vec![];
        for env in self.runtime_context.iter_environments_from_top() {
            let known_left = env.known_equality.get(left_string).map(Rc::clone);
            let known_right = env.known_equality.get(right_string).map(Rc::clone);
            pairs.push((known_left, known_right));
        }
        pairs
    }

    fn try_verify_equality_with_known(
        &mut self,
        equal_fact: &EqualFact,
        known_objs_equal_to_left: Option<&Rc<Vec<Obj>>>,
        known_objs_equal_to_right: Option<&Rc<Vec<Obj>>>,
    ) -> Result<Option<NonErrStmtExecResult>, VerifyError> {
        match (known_objs_equal_to_left, known_objs_equal_to_right) {
            (None, None) => Ok(None),
            (Some(known_objs_equal_to_left), None) => {
                for obj in known_objs_equal_to_left.iter() {
                    let result = self.verify_equality_by_builtin_rules(&EqualFact::new(obj.clone(), equal_fact.right.clone(), equal_fact.line_file_index))?;
                    if result.is_true() {
                        return Ok(Some(result));
                    }
                }
                Ok(None)
            },
            (None, Some(known_objs_equal_to_right)) => {
                for obj in known_objs_equal_to_right.iter() {
                    let result = self.verify_equality_by_builtin_rules(&EqualFact::new(equal_fact.left.clone(), obj.clone(), equal_fact.line_file_index))?;
                    if result.is_true() {
                        return Ok(Some(result));
                    }
                }
                Ok(None)
            }
            (Some(known_objs_equal_to_left), Some(known_objs_equal_to_right)) => {
                for obj1 in known_objs_equal_to_left.iter() {
                    for obj2 in known_objs_equal_to_right.iter() {
                        let result = self.verify_equality_by_builtin_rules(&EqualFact::new(obj1.clone(), obj2.clone(), equal_fact.line_file_index))?;
                        if result.is_true() {
                            return Ok(Some(result));
                        }
                    }
                }
                Ok(None)
            }
        }
    }

    fn verify_equality_with_known_forall_facts(&mut self, equal_fact: &EqualFact, verify_state: &VerifyState) -> Result<NonErrStmtExecResult, VerifyError> {
        _ = verify_state;
        _ = equal_fact;
        return Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()));
    }
}
