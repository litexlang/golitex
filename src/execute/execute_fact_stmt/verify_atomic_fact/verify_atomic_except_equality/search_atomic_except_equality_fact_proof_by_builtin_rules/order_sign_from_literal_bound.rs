//! Prove a sign-vs-0 goal from a known order with a resolved numeric bound.
//!
//! B1 boundary: bound → sign spelling is verify-time only (not eager infer).
//!
//! Example: trust a >= 1; 0 < a.
//! Example: trust a <= -1; a <= 0.

use crate::ast::fact::{LessEqualFact, LessFact};
use crate::ast::obj::{Literal, Number, Obj};
use crate::rational_expression::{compare_number_strings, NumberCompareResult};
use crate::runtime::{FactId, Runtime};

// Builtin: `0 < x` from known `x >= k` or `x > k` with resolved k > 0
// (or known `k <= x` / `k < x` with the same bound on the left).
// Example: trust a >= 1; 0 < a.
pub struct OrderSignFromPositiveLiteralBoundBuiltinRuleProof {
    pub cite_fact_id: FactId,
}

// Builtin: `x <= 0` from known `x <= k` or `x < k` with resolved k < 0
// (or known `k >= x` / `k > x` with the same bound on the left).
// Example: trust a <= -1; a <= 0.
pub struct OrderSignFromNegativeLiteralBoundBuiltinRuleProof {
    pub cite_fact_id: FactId,
}

impl Runtime {
    pub(crate) fn try_order_sign_from_positive_literal_bound(
        &self,
        fact: &LessFact,
    ) -> Option<OrderSignFromPositiveLiteralBoundBuiltinRuleProof> {
        if !is_literal_zero(&fact.left) {
            return None;
        }
        let x = &fact.right;
        let cite_fact_id = self.known_positive_lower_bound_cite(x)?;
        Some(OrderSignFromPositiveLiteralBoundBuiltinRuleProof { cite_fact_id })
    }

    pub(crate) fn try_order_sign_from_negative_literal_bound(
        &self,
        fact: &LessEqualFact,
    ) -> Option<OrderSignFromNegativeLiteralBoundBuiltinRuleProof> {
        if !is_literal_zero(&fact.right) {
            return None;
        }
        let x = &fact.left;
        let cite_fact_id = self.known_negative_upper_bound_cite(x)?;
        Some(OrderSignFromNegativeLiteralBoundBuiltinRuleProof { cite_fact_id })
    }

    fn known_positive_lower_bound_cite(&self, x: &Obj) -> Option<FactId> {
        // Scan known >= and > with x on the left and a positive literal on the right.
        for env in self.execution_environments_stack.iter().rev() {
            let facts = &env.facts.known_atomic_except_equality_facts.by_prop;
            for ((_, _), knowns) in facts.iter() {
                for known in knowns {
                    match known {
                        crate::ast::fact::AtomicFact::GreaterEqualFact(g)
                            if g.left.ir() == x.ir() =>
                        {
                            if bound_is_strictly_positive(self, &g.right) {
                                return Some(g.fact_id);
                            }
                        }
                        crate::ast::fact::AtomicFact::GreaterFact(g)
                            if g.left.ir() == x.ir() =>
                        {
                            if bound_is_nonnegative(self, &g.right) {
                                return Some(g.fact_id);
                            }
                        }
                        crate::ast::fact::AtomicFact::LessEqualFact(l)
                            if l.right.ir() == x.ir() =>
                        {
                            if bound_is_strictly_positive(self, &l.left) {
                                return Some(l.fact_id);
                            }
                        }
                        crate::ast::fact::AtomicFact::LessFact(l)
                            if l.right.ir() == x.ir() =>
                        {
                            if bound_is_nonnegative(self, &l.left) {
                                return Some(l.fact_id);
                            }
                        }
                        _ => {}
                    }
                }
            }
        }
        None
    }

    fn known_negative_upper_bound_cite(&self, x: &Obj) -> Option<FactId> {
        for env in self.execution_environments_stack.iter().rev() {
            let facts = &env.facts.known_atomic_except_equality_facts.by_prop;
            for ((_, _), knowns) in facts.iter() {
                for known in knowns {
                    match known {
                        crate::ast::fact::AtomicFact::LessEqualFact(l)
                            if l.left.ir() == x.ir() =>
                        {
                            if bound_is_strictly_negative(self, &l.right) {
                                return Some(l.fact_id);
                            }
                        }
                        crate::ast::fact::AtomicFact::LessFact(l)
                            if l.left.ir() == x.ir() =>
                        {
                            if bound_is_nonpositive(self, &l.right) {
                                return Some(l.fact_id);
                            }
                        }
                        crate::ast::fact::AtomicFact::GreaterEqualFact(g)
                            if g.right.ir() == x.ir() =>
                        {
                            if bound_is_strictly_negative(self, &g.left) {
                                return Some(g.fact_id);
                            }
                        }
                        crate::ast::fact::AtomicFact::GreaterFact(g)
                            if g.right.ir() == x.ir() =>
                        {
                            if bound_is_nonpositive(self, &g.left) {
                                return Some(g.fact_id);
                            }
                        }
                        _ => {}
                    }
                }
            }
        }
        None
    }
}

fn bound_is_strictly_positive(runtime: &Runtime, obj: &Obj) -> bool {
    runtime
        .resolve_obj_to_normalized_number(obj)
        .map(|n| {
            matches!(
                compare_number_strings(&n, "0"),
                NumberCompareResult::Greater
            )
        })
        .unwrap_or(false)
}

fn bound_is_nonnegative(runtime: &Runtime, obj: &Obj) -> bool {
    runtime
        .resolve_obj_to_normalized_number(obj)
        .map(|n| {
            matches!(
                compare_number_strings(&n, "0"),
                NumberCompareResult::Greater | NumberCompareResult::Equal
            )
        })
        .unwrap_or(false)
}

fn bound_is_strictly_negative(runtime: &Runtime, obj: &Obj) -> bool {
    runtime
        .resolve_obj_to_normalized_number(obj)
        .map(|n| {
            matches!(
                compare_number_strings(&n, "0"),
                NumberCompareResult::Less
            )
        })
        .unwrap_or(false)
}

fn bound_is_nonpositive(runtime: &Runtime, obj: &Obj) -> bool {
    runtime
        .resolve_obj_to_normalized_number(obj)
        .map(|n| {
            matches!(
                compare_number_strings(&n, "0"),
                NumberCompareResult::Less | NumberCompareResult::Equal
            )
        })
        .unwrap_or(false)
}

fn is_literal_zero(obj: &Obj) -> bool {
    matches!(
        obj,
        Obj::Literal(Literal::Number(Number { normalized_value })) if normalized_value == "0"
    )
}
