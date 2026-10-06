//! Fixed first-quadrant facts; all mathematical premises are actual known bounds.
use super::less::LessFactSearchProofByBuiltinRule;
use super::greater::GreaterFactSearchProofByBuiltinRule;
use crate::ast::fact::{LessFact, GreaterFact};
use crate::ast::obj::{Obj, TrigOperator};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::AtomicExceptEqualityFactKnownProof;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_inverse_trig::{half_pi, zero_obj};
use crate::runtime::Runtime;

// For real x, 0<x<pi/2 implies cos(x)!=0. Endpoints are excluded.
pub struct CosNonzeroOnFirstQuadrantProof {
    pub lower_bound_proof: AtomicExceptEqualityFactKnownProof,
    pub upper_bound_proof: AtomicExceptEqualityFactKnownProof,
}

// For real x, 0<x<pi/2 implies sin(x)!=0. Endpoints are excluded.
pub struct SinNonzeroOnFirstQuadrantProof {
    pub lower_bound_proof: AtomicExceptEqualityFactKnownProof,
    pub upper_bound_proof: AtomicExceptEqualityFactKnownProof,
}

// For real x, 0<x<pi/2 implies 0<tan(x). Endpoints are excluded.
pub struct TanPositiveOnFirstQuadrantProof {
    pub lower_bound_proof: AtomicExceptEqualityFactKnownProof,
    pub upper_bound_proof: AtomicExceptEqualityFactKnownProof,
}

// For real x, 0<x<pi/2 implies 0<cot(x). Endpoints are excluded.
pub struct CotPositiveOnFirstQuadrantProof {
    pub lower_bound_proof: AtomicExceptEqualityFactKnownProof,
    pub upper_bound_proof: AtomicExceptEqualityFactKnownProof,
}

// For real x, 0<x<pi/2 implies tan(x)>0. Endpoints are excluded.
pub struct TanGreaterZeroOnFirstQuadrantProof {
    pub lower_bound_proof: AtomicExceptEqualityFactKnownProof,
    pub upper_bound_proof: AtomicExceptEqualityFactKnownProof,
}

// For real x, 0<x<pi/2 implies cot(x)>0. Endpoints are excluded.
pub struct CotGreaterZeroOnFirstQuadrantProof {
    pub lower_bound_proof: AtomicExceptEqualityFactKnownProof,
    pub upper_bound_proof: AtomicExceptEqualityFactKnownProof,
}

impl Runtime {
    pub(super) fn search_first_quadrant_positive_less(&mut self, fact: &LessFact) -> Option<LessFactSearchProofByBuiltinRule> {
        if fact.left.ir() != zero_obj().ir() { return None; }
        match &fact.right {
            Obj::TrigOperator(TrigOperator::Tan(value)) => {
                let (lower_bound_proof, upper_bound_proof) = self.first_quadrant_bounds_for_arg(&value.arg)?;
                Some(LessFactSearchProofByBuiltinRule::TanPositiveOnFirstQuadrant(TanPositiveOnFirstQuadrantProof { lower_bound_proof, upper_bound_proof }))
            }
            Obj::TrigOperator(TrigOperator::Cot(value)) => {
                let (lower_bound_proof, upper_bound_proof) = self.first_quadrant_bounds_for_arg(&value.arg)?;
                Some(LessFactSearchProofByBuiltinRule::CotPositiveOnFirstQuadrant(CotPositiveOnFirstQuadrantProof { lower_bound_proof, upper_bound_proof }))
            }
            _ => None,
        }
    }

    pub(super) fn search_first_quadrant_positive_greater(&mut self, fact: &GreaterFact) -> Option<GreaterFactSearchProofByBuiltinRule> {
        if fact.right.ir() != zero_obj().ir() { return None; }
        match &fact.left {
            Obj::TrigOperator(TrigOperator::Tan(value)) => {
                let (lower_bound_proof, upper_bound_proof) = self.first_quadrant_bounds_for_arg(&value.arg)?;
                Some(GreaterFactSearchProofByBuiltinRule::TanGreaterZeroOnFirstQuadrant(TanGreaterZeroOnFirstQuadrantProof { lower_bound_proof, upper_bound_proof }))
            }
            Obj::TrigOperator(TrigOperator::Cot(value)) => {
                let (lower_bound_proof, upper_bound_proof) = self.first_quadrant_bounds_for_arg(&value.arg)?;
                Some(GreaterFactSearchProofByBuiltinRule::CotGreaterZeroOnFirstQuadrant(CotGreaterZeroOnFirstQuadrantProof { lower_bound_proof, upper_bound_proof }))
            }
            _ => None,
        }
    }

    // Read-only known-fact lookup: same argument identity, two fixed endpoints,
    // two actual comparison orientations. No search, publication, or state reset.
    pub(super) fn first_quadrant_bounds_for_arg(&mut self, arg: &Obj)
        -> Option<(AtomicExceptEqualityFactKnownProof, AtomicExceptEqualityFactKnownProof)> {
        let lower_bound_proof = self.known_less_proof(&zero_obj(), arg)
            .or_else(|| self.known_greater_proof(arg, &zero_obj()))?;
        let upper_bound_proof = self.known_less_proof(arg, &half_pi())
            .or_else(|| self.known_greater_proof(&half_pi(), arg))?;
        Some((lower_bound_proof, upper_bound_proof))
    }
}

#[cfg(test)]
#[path = "../../../../../../tests/unit/execute/trig_first_quadrant/tests.rs"]
mod trig_first_quadrant_tests;
