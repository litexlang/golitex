use crate::calculate_and_simplify_rational_expression::objs_equal_by_rational_expression_simplification;
use crate::error::VerifyError;
use crate::execute::Runtime;
use crate::fact::{AtomicFact, IsNonemptySetFact, NotEqualFact};
use crate::infer::InferResult;
use crate::obj::Obj;
use crate::result::FactVerifiedByBuiltinRules;
use crate::result::NonErrStmtExecResult;
use crate::result::StmtUnknown;
use crate::verify::verify_number_comparison_builtin_rule::verify_number_comparison_builtin_rule;
use crate::verify::VerifyState;

impl<'a> Runtime<'a> {
    pub fn verify_non_equational_atomic_fact_with_builtin_rules(
        &mut self,
        atomic_fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<NonErrStmtExecResult, VerifyError> {
        match atomic_fact {
            AtomicFact::EqualFact(_) => unreachable!(),
            AtomicFact::NotEqualFact(not_equal_fact) => {
                self._verify_not_equal_fact_with_builtin_rules(not_equal_fact, verify_state)
            }
            AtomicFact::InFact(in_fact) => {
                self.verify_in_fact_with_builtin_rules(in_fact, verify_state)
            }
            AtomicFact::LessFact(_)
            | AtomicFact::GreaterFact(_)
            | AtomicFact::LessEqualFact(_)
            | AtomicFact::GreaterEqualFact(_) => {
                let number_compare_result = verify_number_comparison_builtin_rule(atomic_fact);
                match number_compare_result {
                    Some(true) => Ok(NonErrStmtExecResult::FactVerifiedByBuiltinRules(
                        crate::result::FactVerifiedByBuiltinRules::new(
                            atomic_fact.to_string(),
                            "number comparison".to_string(),
                            InferResult::new(),
                            atomic_fact.line_file(),
                        ),
                    )),
                    Some(false) => Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new())),
                    None => Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new())),
                }
            }
            AtomicFact::IsSetFact(is_set_fact) => Ok(
                NonErrStmtExecResult::FactVerifiedByBuiltinRules(FactVerifiedByBuiltinRules::new(
                    is_set_fact.to_string(),
                    "Every object is a set.".to_string(),
                    InferResult::new(),
                    is_set_fact.line_file,
                )),
            ),
            AtomicFact::RestrictFact(restrict_fact) => {
                self.verify_restrict_fact_with_builtin_rules(restrict_fact, verify_state)
            }
            AtomicFact::IsNonemptySetFact(is_nonempty_set_fact) => self
                ._verify_is_nonempty_set_fact_with_builtin_rules(
                    is_nonempty_set_fact,
                    verify_state,
                ),
            _ => Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new())),
        }
    }

    fn _verify_not_equal_fact_with_builtin_rules(
        &mut self,
        not_equal_fact: &NotEqualFact,
        _verify_state: &VerifyState,
    ) -> Result<NonErrStmtExecResult, VerifyError> {
        let left_obj = &not_equal_fact.left;
        let right_obj = &not_equal_fact.right;

        if left_obj.can_be_calculated() && right_obj.can_be_calculated() {
            if left_obj.two_objs_can_be_calculated_and_equal_by_calculation(right_obj) {
                return Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()));
            }
            return Ok(NonErrStmtExecResult::FactVerifiedByBuiltinRules(
                FactVerifiedByBuiltinRules::new(
                    not_equal_fact.to_string(),
                    "calculation".to_string(),
                    InferResult::new(),
                    not_equal_fact.line_file,
                ),
            ));
        }

        if left_obj.can_be_calculated() && right_obj.can_be_calculated() {
            if objs_equal_by_rational_expression_simplification(left_obj, right_obj) {
                return Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()));
            }
            return Ok(NonErrStmtExecResult::FactVerifiedByBuiltinRules(
                FactVerifiedByBuiltinRules::new(
                    not_equal_fact.to_string(),
                    "rational expression simplification".to_string(),
                    InferResult::new(),
                    not_equal_fact.line_file,
                ),
            ));
        }

        Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()))
    }

    fn _verify_is_nonempty_set_fact_with_builtin_rules(
        &mut self,
        is_nonempty_set_fact: &IsNonemptySetFact,
        _verify_state: &VerifyState,
    ) -> Result<NonErrStmtExecResult, VerifyError> {
        match &is_nonempty_set_fact.set {
            Obj::NPosObj(_)
            | Obj::NObj(_)
            | Obj::QObj(_)
            | Obj::RObj(_)
            | Obj::RNz(_)
            | Obj::ZNz(_)
            | Obj::QNz(_)
            | Obj::QPos(_)
            | Obj::RPos(_)
            | Obj::RNeg(_)
            | Obj::ZNeg(_)
            | Obj::QNeg(_)
            | Obj::ZObj(_) => Ok(NonErrStmtExecResult::FactVerifiedByBuiltinRules(
                FactVerifiedByBuiltinRules::new(
                    is_nonempty_set_fact.to_string(),
                    "standard_nonempty_set".to_string(),
                    InferResult::new(),
                    is_nonempty_set_fact.line_file,
                ),
            )),
            Obj::Cart(cart) => {
                for arg_obj in &cart.args {
                    let is_nonempty_set_result = self
                        .verify_non_equational_atomic_fact_with_builtin_rules(
                            &AtomicFact::IsNonemptySetFact(IsNonemptySetFact::new(
                                *arg_obj.clone(),
                                is_nonempty_set_fact.line_file,
                            )),
                            _verify_state,
                        )?;

                    if is_nonempty_set_result.is_unknown() {
                        return Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()));
                    }
                }

                // verified by objects in cart are all nonempty sets
                Ok(NonErrStmtExecResult::FactVerifiedByBuiltinRules(
                    FactVerifiedByBuiltinRules::new(
                        is_nonempty_set_fact.to_string(),
                        "cart_nonempty_set".to_string(),
                        InferResult::new(),
                        is_nonempty_set_fact.line_file,
                    ),
                ))
            }
            _ => Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new())),
        }
    }
}
