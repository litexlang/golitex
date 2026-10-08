//! Fixed real metric bounds; parent WD owns every scalar domain.
use crate::prelude::*;
use super::helper::{binary_extremum_operands, BinaryExtremumKind};
use super::less_equal::LessEqualFactSearchProofByBuiltinRule;

pub struct AbsDifferenceTriangleProof {}
impl AbsDifferenceTriangleProof {
    pub fn new() -> Self { Self {} }
}

pub struct MaxLipschitzFromCoordinateBoundsProof {
    pub left_error_bound: VerifyFactResult,
    pub right_error_bound: VerifyFactResult,
}
impl MaxLipschitzFromCoordinateBoundsProof {
    pub fn new(left_error_bound: VerifyFactResult, right_error_bound: VerifyFactResult) -> Self {
        Self { left_error_bound, right_error_bound }
    }
}

pub struct MinLipschitzFromCoordinateBoundsProof {
    pub left_error_bound: VerifyFactResult,
    pub right_error_bound: VerifyFactResult,
}
impl MinLipschitzFromCoordinateBoundsProof {
    pub fn new(left_error_bound: VerifyFactResult, right_error_bound: VerifyFactResult) -> Self {
        Self { left_error_bound, right_error_bound }
    }
}

impl Runtime {
    pub(super) fn search_real_metric_bound(
        &mut self,
        fact: &LessEqualFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<LessEqualFactSearchProofByBuiltinRule>> {
        use LessEqualFactSearchProofByBuiltinRule as P;
        let Obj::ArithmeticOperator(ArithmeticOperator::Abs(abs)) = &fact.left else {
            return Ok(None);
        };
        let Obj::ArithmeticOperator(ArithmeticOperator::Sub(difference)) = &*abs.arg else {
            return Ok(None);
        };

        // Real distance satisfies |x-z| <= |x-y|+|y-z|. Also accept
        // |x-y| <= |x|+|y|. Only a fixed number of structural orientations
        // are inspected; no rewrite or intermediate point is discovered.
        if abs_difference_triangle_matches(&difference.left, &difference.right, &fact.right) {
            return Ok(Some(P::AbsDifferenceTriangle(AbsDifferenceTriangleProof::new())));
        }

        let Some((left_kind, a, b)) = binary_extremum_operands(&difference.left) else {
            return Ok(None);
        };
        let Some((right_kind, x, y)) = binary_extremum_operands(&difference.right) else {
            return Ok(None);
        };
        if left_kind != right_kind { return Ok(None); }

        // |a-x|<=epsilon and |b-y|<=epsilon imply that the two minima
        // (or maxima) differ by at most epsilon. The goal supplies epsilon;
        // retain both independently checked bounds at the inherited ceiling.
        // Example: abs(max(a,b)-max(x,y)) <= epsilon.
        let Some(left_error_bound) = self.metric_error_bound(a, x, &fact.right, fact, state)?
        else { return Ok(None); };
        let Some(right_error_bound) = self.metric_error_bound(b, y, &fact.right, fact, state)?
        else { return Ok(None); };
        Ok(Some(match left_kind {
            BinaryExtremumKind::Maximum => P::MaxLipschitzFromCoordinateBounds(
                MaxLipschitzFromCoordinateBoundsProof::new(left_error_bound, right_error_bound)),
            BinaryExtremumKind::Minimum => P::MinLipschitzFromCoordinateBounds(
                MinLipschitzFromCoordinateBoundsProof::new(left_error_bound, right_error_bound)),
        }))
    }

    fn metric_error_bound(
        &mut self,
        left: &Obj,
        right: &Obj,
        bound: &Obj,
        source: &LessEqualFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<VerifyFactResult>> {
        let difference = Obj::ArithmeticOperator(ArithmeticOperator::Sub(Sub {
            left: Box::new(left.clone()), right: Box::new(right.clone()),
        }));
        let absolute_error = Obj::ArithmeticOperator(ArithmeticOperator::Abs(Abs {
            arg: Box::new(difference),
        }));
        if let Some(proof) = self.weak_order_premise(
            &absolute_error, bound, source.line_file.clone(), state,
        )? {
            return Ok(Some(proof));
        }
        // A strict bound is also sufficient. Cite its actual orientation;
        // do not start a <= conversion rule below the premise ceiling.
        self.strict_order_premise(&absolute_error, bound, source.line_file.clone(), state)
    }
}

fn abs_difference_triangle_matches(a: &Obj, c: &Obj, bound: &Obj) -> bool {
    let Obj::ArithmeticOperator(ArithmeticOperator::Add(sum)) = bound else { return false; };
    for (left, right) in [(&*sum.left, &*sum.right), (&*sum.right, &*sum.left)] {
        let (Obj::ArithmeticOperator(ArithmeticOperator::Abs(left)),
             Obj::ArithmeticOperator(ArithmeticOperator::Abs(right))) = (left, right)
        else { continue; };
        if left.arg.ir() == a.ir() && right.arg.ir() == c.ir() { return true; }
        let (Obj::ArithmeticOperator(ArithmeticOperator::Sub(first)),
             Obj::ArithmeticOperator(ArithmeticOperator::Sub(second))) = (&*left.arg, &*right.arg)
        else { continue; };
        for (x, y) in [(&*first.left, &*first.right), (&*first.right, &*first.left)] {
            for (middle, z) in [(&*second.left, &*second.right), (&*second.right, &*second.left)] {
                if y.ir() == middle.ir()
                    && ((x.ir() == a.ir() && z.ir() == c.ir())
                        || (x.ir() == c.ir() && z.ir() == a.ir())) {
                    return true;
                }
            }
        }
    }
    false
}

#[cfg(test)]
#[path = "../../../../../../tests/unit/execute/real_metric_bounds/tests.rs"]
mod real_metric_bounds_tests;
