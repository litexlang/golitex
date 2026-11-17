//! Convex combinations belong to their real segment, with explicit endpoint exclusions.
use crate::execute::execute_fact_stmt::riemann_integral::helper::{lt, member, num, real};
use crate::prelude::*;

pub struct RealSegmentMembershipProof {
    pub requirements: Vec<Fact>,
    pub proofs: Vec<VerifyFactResult>,
}

impl Runtime {
    // a+t*(b-a) belongs to the segment from a to b when 0<t<1.
    // Excluding either extreme is sound when a!=b. Included endpoints are
    // handled by the same rule with the exact list of excluded points.
    pub(crate) fn real_segment_membership(
        &mut self,
        fact: &InFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<RealSegmentMembershipProof>> {
        let (interval, excluded) = match &fact.set {
            Obj::SetOperator(SetOperator::SetMinus(difference)) => {
                let Obj::SetFormer(SetFormer::ListSet(excluded)) = difference.right.as_ref() else {
                    return Ok(None);
                };
                (difference.left.as_ref(), excluded.list.as_slice())
            }
            interval => (interval, &[][..]),
        };
        let Obj::SetFormer(SetFormer::IntervalObj(IntervalObj::LeftClosedRightClosed(interval))) =
            interval
        else {
            return Ok(None);
        };
        let (
            Obj::ArithmeticOperator(ArithmeticOperator::Min(lower)),
            Obj::ArithmeticOperator(ArithmeticOperator::Max(upper)),
        ) = (interval.start.as_ref(), interval.end.as_ref())
        else {
            return Ok(None);
        };
        if lower.left != upper.left || lower.right != upper.right {
            return Ok(None);
        }
        let a = lower.left.as_ref();
        let b = lower.right.as_ref();
        if !excluded
            .iter()
            .all(|point| point.as_ref() == a || point.as_ref() == b)
        {
            return Ok(None);
        }
        let mut requirements = vec![
            member(self, a.clone(), real()).into(),
            member(self, b.clone(), real()).into(),
        ];
        let midpoint = is_midpoint(&fact.element, a, b);
        if &fact.element == a || &fact.element == b {
            if excluded.iter().any(|point| point.as_ref() == &fact.element) {
                return Ok(None);
            }
        } else if !midpoint {
            let Obj::ArithmeticOperator(ArithmeticOperator::Add(sum)) = &fact.element else {
                return Ok(None);
            };
            let start = sum.left.as_ref();
            let Obj::ArithmeticOperator(ArithmeticOperator::Mul(product)) = sum.right.as_ref()
            else {
                return Ok(None);
            };
            let Obj::ArithmeticOperator(ArithmeticOperator::Sub(difference)) =
                product.right.as_ref()
            else {
                return Ok(None);
            };
            let end = difference.left.as_ref();
            if difference.right.as_ref() != start
                || !segment_anchor(start, a, b)
                || !segment_anchor(end, a, b)
                || (start == end && !is_midpoint(start, a, b))
            {
                return Ok(None);
            }
            let parameter = product.left.as_ref();
            requirements.extend([
                member(self, parameter.clone(), real()).into(),
                lt(self, num("0"), parameter.clone()).into(),
                lt(self, parameter.clone(), num("1")).into(),
            ]);
        }
        if !excluded.is_empty() {
            requirements.push(
                NotEqualFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    left: a.clone(),
                    right: b.clone(),
                    line_file: None,
                }
                .into(),
            );
        }
        let mut proofs = Vec::new();
        for requirement in &requirements {
            let proof = self.verify_fact(requirement, state)?;
            if proof.is_failed() {
                return Ok(None);
            }
            proofs.push(proof);
        }
        Ok(Some(RealSegmentMembershipProof {
            requirements,
            proofs,
        }))
    }
}

fn segment_anchor(point: &Obj, a: &Obj, b: &Obj) -> bool {
    point == a || point == b || is_midpoint(point, a, b)
}

fn is_midpoint(point: &Obj, a: &Obj, b: &Obj) -> bool {
    let Obj::ArithmeticOperator(ArithmeticOperator::Div(quotient)) = point else {
        return false;
    };
    let Obj::ArithmeticOperator(ArithmeticOperator::Add(sum)) = quotient.left.as_ref() else {
        return false;
    };
    quotient.right.as_ref() == &num("2")
        && ((sum.left.as_ref() == a && sum.right.as_ref() == b)
            || (sum.left.as_ref() == b && sum.right.as_ref() == a))
}
