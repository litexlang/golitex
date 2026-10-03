use crate::ast::fact::{
    atomic_fact_args_ref, AtomicFact, Fact, GreaterFact, InFact, IsFiniteSetFact,
    IsNonemptySetFact, LessEqualFact, LessFact, NotEqualFact, NotInFact, SubsetFact,
};
use crate::ast::line_file::SourceLine;
use crate::ast::obj::{Literal, Number, Obj};
use crate::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::execute::execute_fact_stmt::verify_state::VerifyState;
use crate::runtime::{Runtime, RuntimeResult};
use std::cell::RefCell;

// Break strategy → verify_fact → strategy cycles (e.g. nonempty(closed_range(a,b))
// requiring a <= b while a nested search re-enters the same nonempty goal).
thread_local! {
    static BUILTIN_STRATEGY_GOAL_STACK: RefCell<Vec<String>> = RefCell::new(Vec::new());
}

pub(super) fn strategy_goal_key(fact: &AtomicFact) -> String {
    let args: Vec<String> = atomic_fact_args_ref(fact)
        .iter()
        .map(|obj| format!("{}", obj.ir()))
        .collect();
    format!("{}:{}", fact.prop_name(), args.join(","))
}

pub(super) fn enter_strategy_goal(key: &str) -> bool {
    BUILTIN_STRATEGY_GOAL_STACK.with(|stack| {
        let mut stack = stack.borrow_mut();
        if stack.iter().any(|seen| seen == key) {
            return false;
        }
        stack.push(key.to_string());
        true
    })
}

pub(super) fn leave_strategy_goal(key: &str) {
    BUILTIN_STRATEGY_GOAL_STACK.with(|stack| {
        let mut stack = stack.borrow_mut();
        if stack.last().map(|s| s.as_str()) == Some(key) {
            stack.pop();
        } else {
            stack.retain(|seen| seen != key);
        }
    });
}

pub(super) fn zero_obj() -> Obj {
    Obj::Literal(Literal::Number(Number {
        normalized_value: "0".to_string(),
    }))
}

pub(super) fn one_obj() -> Obj {
    Obj::Literal(Literal::Number(Number {
        normalized_value: "1".to_string(),
    }))
}

pub(super) fn two_obj() -> Obj {
    Obj::Literal(Literal::Number(Number {
        normalized_value: "2".to_string(),
    }))
}

pub(super) fn is_zero_obj(obj: &Obj) -> bool {
    matches!(
        obj,
        Obj::Literal(Literal::Number(Number {
            normalized_value,
        })) if normalized_value == "0"
    )
}


impl Runtime {
    // Prove strategy premises inside VerifyState: known + nested strategy only.
    pub(crate) fn verify_strategy_requirements(
        &mut self,
        requirement_facts: Vec<Fact>,
        ctx: VerifyState,
    ) -> RuntimeResult<Option<(Vec<Fact>, Vec<VerifyFactResult>)>> {
        let child = ctx;
        let mut proof_of_requirement_facts = Vec::with_capacity(requirement_facts.len());
        for requirement in &requirement_facts {
            let proof = self.verify_fact(requirement, child)?;
            if proof.is_failed() {
                return Ok(None);
            }
            proof_of_requirement_facts.push(proof);
        }
        Ok(Some((requirement_facts, proof_of_requirement_facts)))
    }

    pub(crate) fn try_strategy_requirement_alternatives(
        &mut self,
        alternatives: Vec<Vec<Fact>>,
        ctx: VerifyState,
    ) -> RuntimeResult<Option<(Vec<Fact>, Vec<VerifyFactResult>)>> {
        for required in alternatives {
            if let Some(ok) = self.verify_strategy_requirements(required, ctx)? {
                return Ok(Some(ok));
            }
        }
        Ok(None)
    }

    pub(super) fn strategy_less_fact(
        &mut self,
        left: Obj,
        right: Obj,
        line_file: Option<SourceLine>,
    ) -> Fact {
        LessFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left,
            right,
            line_file,
        }
        .into()
    }

    pub(super) fn strategy_greater_fact(
        &mut self,
        left: Obj,
        right: Obj,
        line_file: Option<SourceLine>,
    ) -> Fact {
        GreaterFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left,
            right,
            line_file,
        }
        .into()
    }

    pub(super) fn strategy_less_equal_fact(
        &mut self,
        left: Obj,
        right: Obj,
        line_file: Option<SourceLine>,
    ) -> Fact {
        LessEqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left,
            right,
            line_file,
        }
        .into()
    }


    pub(super) fn strategy_not_equal_fact(
        &mut self,
        left: Obj,
        right: Obj,
        line_file: Option<SourceLine>,
    ) -> Fact {
        NotEqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left,
            right,
            line_file,
        }
        .into()
    }

    pub(super) fn strategy_in_fact(
        &mut self,
        element: Obj,
        set: Obj,
        line_file: Option<SourceLine>,
    ) -> Fact {
        InFact {
            fact_id: self.global_ids.allocate_fact_id(),
            element,
            set,
            line_file,
        }
        .into()
    }

    pub(super) fn strategy_not_in_fact(
        &mut self,
        element: Obj,
        set: Obj,
        line_file: Option<SourceLine>,
    ) -> Fact {
        NotInFact {
            fact_id: self.global_ids.allocate_fact_id(),
            element,
            set,
            line_file,
        }
        .into()
    }

    pub(super) fn strategy_subset_fact(
        &mut self,
        left: Obj,
        right: Obj,
        line_file: Option<SourceLine>,
    ) -> Fact {
        SubsetFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left,
            right,
            line_file,
        }
        .into()
    }

    pub(super) fn strategy_is_finite_set_fact(
        &mut self,
        set: Obj,
        line_file: Option<SourceLine>,
    ) -> Fact {
        IsFiniteSetFact {
            fact_id: self.global_ids.allocate_fact_id(),
            set,
            line_file,
        }
        .into()
    }

    pub(super) fn strategy_is_nonempty_set_fact(
        &mut self,
        set: Obj,
        line_file: Option<SourceLine>,
    ) -> Fact {
        IsNonemptySetFact {
            fact_id: self.global_ids.allocate_fact_id(),
            set,
            line_file,
        }
        .into()
    }
}


// Zero is also 0/c once the caller proves the strict sign of c. This lets
// quotient monotonicity handle 0 <= a/c and a/c <= 0 without a manual 0/c bridge.
// The caller must retain the denominator-sign and numerator-order proofs.
pub(super) fn common_division_parts(left: &Obj, right: &Obj) -> Option<(Obj, Obj, Obj)> {
    use crate::ast::obj::ArithmeticOperator;
    match (left, right) {
        (Obj::ArithmeticOperator(ArithmeticOperator::Div(a)), Obj::ArithmeticOperator(ArithmeticOperator::Div(b)))
            if a.right == b.right => Some((*a.left.clone(), *b.left.clone(), *a.right.clone())),
        (_, Obj::ArithmeticOperator(ArithmeticOperator::Div(b))) if is_zero_obj(left) =>
            Some((zero_obj(), *b.left.clone(), *b.right.clone())),
        (Obj::ArithmeticOperator(ArithmeticOperator::Div(a)), _) if is_zero_obj(right) =>
            Some((*a.left.clone(), zero_obj(), *a.right.clone())),
        _ => None,
    }
}
