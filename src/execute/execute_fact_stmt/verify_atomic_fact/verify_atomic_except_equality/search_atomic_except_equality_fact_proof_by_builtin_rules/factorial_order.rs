//! Natural factorial preserves weak order and strict order above the 0/1 boundary.
use crate::ast::fact::{Fact, GreaterEqualFact, GreaterFact, InFact, LessEqualFact, LessFact};
use crate::ast::obj::{IntegerOperator, Obj, StandardSet};
use crate::execute::execute_fact_stmt::{VerifyFactResult, VerifyState};
use crate::runtime::{Runtime, RuntimeResult};

pub struct FactorialMonotoneProof {
    pub argument_order: VerifyFactResult,
}

impl FactorialMonotoneProof {
    pub fn new(argument_order: VerifyFactResult) -> Self { Self { argument_order } }
}

pub struct FactorialStrictMonotoneProof {
    pub positive_smaller: VerifyFactResult,
    pub argument_order: VerifyFactResult,
}

impl FactorialStrictMonotoneProof {
    pub fn new(positive_smaller: VerifyFactResult, argument_order: VerifyFactResult) -> Self {
        Self { positive_smaller, argument_order }
    }
}

impl Runtime {
    pub(super) fn search_factorial_weak_order(
        &mut self, fact: &LessEqualFact, state: VerifyState,
    ) -> RuntimeResult<Option<FactorialMonotoneProof>> {
        // m,n in N and m<=n imply factorial(m)<=factorial(n).
        // Parent fact WD owns the two natural-argument obligations.
        let (Obj::IntegerOperator(IntegerOperator::Factorial(m)),
             Obj::IntegerOperator(IntegerOperator::Factorial(n))) = (&fact.left, &fact.right)
        else { return Ok(None); };
        let premise: Fact = LessEqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: *m.arg.clone(), right: *n.arg.clone(), line_file: fact.line_file.clone(),
        }.into();
        let mut argument_order = self.verify_builtin_rule_premise(&premise, state)?;
        if argument_order.is_failed() {
            // Cite the actual reverse-written premise without requesting an
            // additional builtin direction conversion below the parent ceiling.
            let reverse: Fact = GreaterEqualFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left: *n.arg.clone(), right: *m.arg.clone(), line_file: fact.line_file.clone(),
            }.into();
            argument_order = self.verify_builtin_rule_premise(&reverse, state)?;
        }
        if argument_order.is_failed() { return Ok(None); }
        Ok(Some(FactorialMonotoneProof::new(argument_order)))
    }

    pub(super) fn search_factorial_strict_order(
        &mut self, fact: &LessFact, state: VerifyState,
    ) -> RuntimeResult<Option<FactorialStrictMonotoneProof>> {
        // m in N+, n in N and m<n imply factorial(m)<factorial(n).
        // factorial(0)=factorial(1)=1 forbids an unconditional strict rule.
        let (Obj::IntegerOperator(IntegerOperator::Factorial(m)),
             Obj::IntegerOperator(IntegerOperator::Factorial(n))) = (&fact.left, &fact.right)
        else { return Ok(None); };
        let positive: Fact = InFact {
            fact_id: self.global_ids.allocate_fact_id(), element: *m.arg.clone(),
            set: Obj::StandardSet(StandardSet::NPos), line_file: fact.line_file.clone(),
        }.into();
        let positive_smaller = self.verify_builtin_rule_premise(&positive, state)?;
        if positive_smaller.is_failed() { return Ok(None); }
        let premise: Fact = LessFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: *m.arg.clone(), right: *n.arg.clone(), line_file: fact.line_file.clone(),
        }.into();
        let mut argument_order = self.verify_builtin_rule_premise(&premise, state)?;
        if argument_order.is_failed() {
            let reverse: Fact = GreaterFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left: *n.arg.clone(), right: *m.arg.clone(), line_file: fact.line_file.clone(),
            }.into();
            argument_order = self.verify_builtin_rule_premise(&reverse, state)?;
        }
        if argument_order.is_failed() { return Ok(None); }
        Ok(Some(FactorialStrictMonotoneProof::new(positive_smaller, argument_order)))
    }
}

#[cfg(test)]
#[path = "../../../../../../tests/unit/execute/factorial_lcm_leafs/tests.rs"]
mod factorial_lcm_leaf_tests;
