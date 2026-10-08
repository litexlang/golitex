//! Integer singleton intervals with their exact ordered boundary sources.
use crate::ast::fact::{AtomicFact, EqualFact};
use crate::ast::obj::{Add, ArithmeticOperator as A, Literal, Number, Obj, Sub};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::AtomicExceptEqualityFactKnownProof;
use crate::execute::execute_fact_stmt::{VerifyFactResult, VerifyState};
use crate::rational_expression::{
    exact_rational::EvalRational, objs_equal_by_rational_expression_evaluation,
};
use crate::runtime::{Runtime, RuntimeResult};

pub enum IntegerIntervalEqualityProof {
    SingletonAtLower(IntegerSingletonAtLowerProof),
    SingletonAtUpper(IntegerSingletonAtUpperProof),
}
pub enum IntegerBoundaryProof {
    Membership(VerifyFactResult),
    Successor {
        predecessor: Obj,
        predecessor_integer: VerifyFactResult,
    },
}
pub struct IntegerSingletonAtLowerProof {
    pub variable_integer: VerifyFactResult,
    pub boundary_integer: IntegerBoundaryProof,
    pub lower_weak: AtomicExceptEqualityFactKnownProof,
    pub upper_strict: AtomicExceptEqualityFactKnownProof,
}
impl IntegerSingletonAtLowerProof {
    pub fn new(
        variable_integer: VerifyFactResult,
        boundary_integer: IntegerBoundaryProof,
        lower_weak: AtomicExceptEqualityFactKnownProof,
        upper_strict: AtomicExceptEqualityFactKnownProof,
    ) -> Self {
        Self {
            variable_integer,
            boundary_integer,
            lower_weak,
            upper_strict,
        }
    }
}
pub struct IntegerSingletonAtUpperProof {
    pub variable_integer: VerifyFactResult,
    pub boundary_integer: IntegerBoundaryProof,
    pub lower_strict: AtomicExceptEqualityFactKnownProof,
    pub upper_weak: AtomicExceptEqualityFactKnownProof,
}
impl IntegerSingletonAtUpperProof {
    pub fn new(
        variable_integer: VerifyFactResult,
        boundary_integer: IntegerBoundaryProof,
        lower_strict: AtomicExceptEqualityFactKnownProof,
        upper_weak: AtomicExceptEqualityFactKnownProof,
    ) -> Self {
        Self {
            variable_integer,
            boundary_integer,
            lower_strict,
            upper_weak,
        }
    }
}
impl IntegerIntervalEqualityProof {
    pub fn rule_id(&self) -> &'static str {
        match self {
            Self::SingletonAtLower(_) => "IntegerSingletonAtLower",
            Self::SingletonAtUpper(_) => "IntegerSingletonAtUpper",
        }
    }
}
impl Runtime {
    pub(super) fn search_integer_interval_equality(
        &mut self,
        fact: &EqualFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<IntegerIntervalEqualityProof>> {
        // For integer x,k: k<=x<k+1 implies x=k, and k-1<x<=k
        // implies x=k. Match the four written comparison directions directly.
        for (variable, boundary) in [(&fact.left, &fact.right), (&fact.right, &fact.left)] {
            let next = Obj::ArithmeticOperator(A::Add(Add {
                left: Box::new(boundary.clone()),
                right: Box::new(one()),
            }));
            if let Some(lower_weak) = self.known_integer_interval_order(boundary, variable, false) {
                if let Some(upper_strict) = self.known_integer_interval_order(variable, &next, true)
                {
                    let variable_integer = self.verify_in_integer(variable, state)?;
                    let Some(boundary_integer) = self.integer_interval_boundary(boundary, state)?
                    else {
                        continue;
                    };
                    if !variable_integer.is_failed() {
                        return Ok(Some(IntegerIntervalEqualityProof::SingletonAtLower(
                            IntegerSingletonAtLowerProof::new(
                                variable_integer,
                                boundary_integer,
                                lower_weak,
                                upper_strict,
                            ),
                        )));
                    }
                }
            }
            let previous = Obj::ArithmeticOperator(A::Sub(Sub {
                left: Box::new(boundary.clone()),
                right: Box::new(one()),
            }));
            if let Some(lower_strict) = self.known_integer_interval_order(&previous, variable, true)
            {
                if let Some(upper_weak) =
                    self.known_integer_interval_order(variable, boundary, false)
                {
                    let variable_integer = self.verify_in_integer(variable, state)?;
                    let Some(boundary_integer) = self.integer_interval_boundary(boundary, state)?
                    else {
                        continue;
                    };
                    if !variable_integer.is_failed() {
                        return Ok(Some(IntegerIntervalEqualityProof::SingletonAtUpper(
                            IntegerSingletonAtUpperProof::new(
                                variable_integer,
                                boundary_integer,
                                lower_strict,
                                upper_weak,
                            ),
                        )));
                    }
                }
            }
        }
        Ok(None)
    }

    pub(crate) fn known_integer_interval_order(
        &mut self,
        left: &Obj,
        right: &Obj,
        strict: bool,
    ) -> Option<AtomicExceptEqualityFactKnownProof> {
        // Search the fixed pair of endpoints in stored order facts only. Pure
        // arithmetic matching accepts n+1 / 1+n and closed negative literals.
        let mut selected = None;
        for env in self.execution_environments_stack.iter().rev() {
            for knowns in env
                .facts
                .known_atomic_except_equality_facts
                .by_prop
                .values()
            {
                for known in knowns {
                    let endpoints = match known {
                        AtomicFact::LessFact(f) if strict => Some((&f.left, &f.right)),
                        AtomicFact::GreaterFact(f) if strict => Some((&f.right, &f.left)),
                        AtomicFact::LessEqualFact(f) if !strict => Some((&f.left, &f.right)),
                        AtomicFact::GreaterEqualFact(f) if !strict => Some((&f.right, &f.left)),
                        _ => None,
                    };
                    if let Some((a, b)) = endpoints {
                        if objs_equal_by_rational_expression_evaluation(a, left)
                            && objs_equal_by_rational_expression_evaluation(b, right)
                        {
                            selected = Some(known.clone());
                            break;
                        }
                    }
                }
                if selected.is_some() {
                    break;
                }
            }
            if selected.is_some() {
                break;
            }
        }
        self.lookup_known_atomic_premise(selected?)
    }

    fn integer_interval_boundary(
        &mut self,
        boundary: &Obj,
        state: VerifyState,
    ) -> RuntimeResult<Option<IntegerBoundaryProof>> {
        let member = self.verify_in_integer(boundary, state)?;
        if !member.is_failed() {
            return Ok(Some(IntegerBoundaryProof::Membership(member)));
        }
        // A one-step successor of an integer is integer. This local structural
        // certificate does not re-enter the global membership stage below its cap.
        if let Obj::ArithmeticOperator(A::Add(sum)) = boundary {
            for (predecessor, unit) in [(&*sum.left, &*sum.right), (&*sum.right, &*sum.left)] {
                if EvalRational::from_obj(unit) != EvalRational::new(1, 1) {
                    continue;
                }
                let predecessor_integer = self.verify_in_integer(predecessor, state)?;
                if !predecessor_integer.is_failed() {
                    return Ok(Some(IntegerBoundaryProof::Successor {
                        predecessor: predecessor.clone(),
                        predecessor_integer,
                    }));
                }
            }
        }
        Ok(None)
    }
}
fn one() -> Obj {
    Obj::Literal(Literal::Number(Number::new("1".into())))
}
