//! Fixed real bounds. Parent WD owns the real operands of floor, ceil and abs.
use crate::prelude::*;

pub struct FloorSumLowerBoundProof;
impl FloorSumLowerBoundProof {
    pub fn new() -> Self {
        Self
    }
}
pub struct FloorSumUpperBoundProof;
impl FloorSumUpperBoundProof {
    pub fn new() -> Self {
        Self
    }
}
pub struct CeilSumUpperBoundProof;
impl CeilSumUpperBoundProof {
    pub fn new() -> Self {
        Self
    }
}
pub struct RealReverseTriangleProof;
impl RealReverseTriangleProof {
    pub fn new() -> Self {
        Self
    }
}

pub(super) fn elementary_bound(
    fact: &LessEqualFact,
) -> Option<LessEqualFactSearchProofByBuiltinRule> {
    // floor(x)+floor(y)<=floor(x+y), for all real x,y.
    if let (
        Obj::ArithmeticOperator(ArithmeticOperator::Add(sum)),
        Obj::ArithmeticOperator(ArithmeticOperator::Floor(total)),
    ) = (&fact.left, &fact.right)
    {
        if let (
            Obj::ArithmeticOperator(ArithmeticOperator::Floor(a)),
            Obj::ArithmeticOperator(ArithmeticOperator::Floor(b)),
            Obj::ArithmeticOperator(ArithmeticOperator::Add(args)),
        ) = (&*sum.left, &*sum.right, &*total.arg)
        {
            if a.arg.ir() == args.left.ir() && b.arg.ir() == args.right.ir() {
                return Some(FloorSumLowerBoundProof::new().into());
            }
        }
    }
    // floor(x+y)<=floor(x)+floor(y)+1; the carry is at most one.
    if let (
        Obj::ArithmeticOperator(ArithmeticOperator::Floor(total)),
        Obj::ArithmeticOperator(ArithmeticOperator::Add(upper)),
    ) = (&fact.left, &fact.right)
    {
        if upper.right.ir() == Obj::Literal(Literal::Number(Number::new("1".into()))).ir() {
            if let (
                Obj::ArithmeticOperator(ArithmeticOperator::Add(sum)),
                Obj::ArithmeticOperator(ArithmeticOperator::Add(args)),
            ) = (&*upper.left, &*total.arg)
            {
                if let (
                    Obj::ArithmeticOperator(ArithmeticOperator::Floor(a)),
                    Obj::ArithmeticOperator(ArithmeticOperator::Floor(b)),
                ) = (&*sum.left, &*sum.right)
                {
                    if a.arg.ir() == args.left.ir() && b.arg.ir() == args.right.ir() {
                        return Some(FloorSumUpperBoundProof::new().into());
                    }
                }
            }
        }
    }
    // ceil(x+y)<=ceil(x)+ceil(y), for all real x,y.
    if let (
        Obj::ArithmeticOperator(ArithmeticOperator::Ceil(total)),
        Obj::ArithmeticOperator(ArithmeticOperator::Add(sum)),
    ) = (&fact.left, &fact.right)
    {
        if let (
            Obj::ArithmeticOperator(ArithmeticOperator::Ceil(a)),
            Obj::ArithmeticOperator(ArithmeticOperator::Ceil(b)),
            Obj::ArithmeticOperator(ArithmeticOperator::Add(args)),
        ) = (&*sum.left, &*sum.right, &*total.arg)
        {
            if a.arg.ir() == args.left.ir() && b.arg.ir() == args.right.ir() {
                return Some(CeilSumUpperBoundProof::new().into());
            }
        }
    }
    // ||x|-|y||<=|x-y|; do not strengthen to a strict inequality.
    if let (
        Obj::ArithmeticOperator(ArithmeticOperator::Abs(outer)),
        Obj::ArithmeticOperator(ArithmeticOperator::Abs(bound)),
    ) = (&fact.left, &fact.right)
    {
        if let (
            Obj::ArithmeticOperator(ArithmeticOperator::Sub(diff)),
            Obj::ArithmeticOperator(ArithmeticOperator::Sub(args)),
        ) = (&*outer.arg, &*bound.arg)
        {
            if let (
                Obj::ArithmeticOperator(ArithmeticOperator::Abs(a)),
                Obj::ArithmeticOperator(ArithmeticOperator::Abs(b)),
            ) = (&*diff.left, &*diff.right)
            {
                if (a.arg.ir() == args.left.ir() && b.arg.ir() == args.right.ir())
                    || (a.arg.ir() == args.right.ir() && b.arg.ir() == args.left.ir())
                {
                    return Some(RealReverseTriangleProof::new().into());
                }
            }
        }
    }
    None
}

impl From<FloorSumLowerBoundProof> for LessEqualFactSearchProofByBuiltinRule {
    fn from(proof: FloorSumLowerBoundProof) -> Self {
        Self::FloorSumLowerBound(proof)
    }
}

impl From<FloorSumUpperBoundProof> for LessEqualFactSearchProofByBuiltinRule {
    fn from(proof: FloorSumUpperBoundProof) -> Self {
        Self::FloorSumUpperBound(proof)
    }
}

impl From<CeilSumUpperBoundProof> for LessEqualFactSearchProofByBuiltinRule {
    fn from(proof: CeilSumUpperBoundProof) -> Self {
        Self::CeilSumUpperBound(proof)
    }
}

impl From<RealReverseTriangleProof> for LessEqualFactSearchProofByBuiltinRule {
    fn from(proof: RealReverseTriangleProof) -> Self {
        Self::RealReverseTriangle(proof)
    }
}
