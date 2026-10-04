//! Transport a stored numeric upper/lower bound through subtraction.
//! The enclosing fact established WD. This leaf only reads known order rows
//! and evaluates closed rational endpoints; it does not search a new premise.

use crate::ast::fact::AtomicFact;
use crate::ast::obj::{ArithmeticOperator, Obj};
use crate::rational_expression::exact_rational::EvalRational;
use crate::rational_expression::NumberCompareResult;
use crate::runtime::{FactId, Runtime};

pub enum BoundDirection {
    Lower,
    Upper,
}

pub struct ClosedSubtractionBoundCertificate {
    pub cite_fact_id: FactId,
    pub source_fact: AtomicFact,
    pub direction: BoundDirection,
    pub normalized_subtrahend: Obj,
    pub translated_bound: Obj,
    pub target_bound: Obj,
}

impl Runtime {
    pub(super) fn search_closed_subtraction_weak_bound(
        &self,
        left: &Obj,
        right: &Obj,
        greater_equal: bool,
    ) -> Option<ClosedSubtractionBoundCertificate> {
        self.closed_subtraction_bound_on_side(left, right, greater_equal)
            .or_else(|| self.closed_subtraction_bound_on_side(right, left, !greater_equal))
    }

    fn closed_subtraction_bound_on_side(
        &self,
        expression: &Obj,
        endpoint: &Obj,
        lower: bool,
    ) -> Option<ClosedSubtractionBoundCertificate> {
        let Obj::ArithmeticOperator(ArithmeticOperator::Sub(sub)) = expression else {
            return None;
        };
        let offset = EvalRational::from_obj(&sub.right)?;
        let target = EvalRational::from_obj(endpoint)?;
        let base_ir = sub.left.ir();
        for env in self.execution_environments_stack.iter().rev() {
            for rows in env
                .facts
                .known_atomic_except_equality_facts
                .by_prop
                .values()
            {
                for source in rows {
                    let (a, b, source_lower, cite_fact_id) = match source {
                        AtomicFact::GreaterEqualFact(f) => (&f.left, &f.right, true, f.fact_id),
                        AtomicFact::GreaterFact(f) => (&f.left, &f.right, true, f.fact_id),
                        AtomicFact::LessEqualFact(f) => (&f.left, &f.right, false, f.fact_id),
                        AtomicFact::LessFact(f) => (&f.left, &f.right, false, f.fact_id),
                        _ => continue,
                    };
                    let bound = if source_lower == lower && a.ir() == base_ir {
                        b
                    } else if source_lower != lower && b.ir() == base_ir {
                        a
                    } else {
                        continue;
                    };
                    let Some(translated) =
                        EvalRational::from_obj(bound).and_then(|value| value.sub(&offset))
                    else {
                        continue;
                    };
                    let sufficient = matches!(
                        translated.compare(&target),
                        Some(NumberCompareResult::Equal)
                    ) || matches!(
                        (lower, translated.compare(&target)),
                        (true, Some(NumberCompareResult::Greater))
                            | (false, Some(NumberCompareResult::Less))
                    );
                    if !sufficient {
                        continue;
                    }
                    return Some(ClosedSubtractionBoundCertificate {
                        cite_fact_id,
                        source_fact: source.clone(),
                        direction: if lower {
                            BoundDirection::Lower
                        } else {
                            BoundDirection::Upper
                        },
                        normalized_subtrahend: offset.to_obj(),
                        translated_bound: translated.to_obj(),
                        target_bound: target.to_obj(),
                    });
                }
            }
        }
        None
    }
}

#[cfg(test)]
#[path = "../../../../../../tests/unit/execute/closed_subtraction_bound/tests.rs"]
mod tests;
