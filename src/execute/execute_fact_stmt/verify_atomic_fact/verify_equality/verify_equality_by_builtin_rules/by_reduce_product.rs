//! A homogeneous multiplication fold with seed one is the same product.
use crate::ast::fact::EqualFact;
use crate::ast::obj::{ArithmeticOperator, FunctionSpace, IdentifierObj, IteratedOperator, Literal, Obj};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_they_are_the_same::helper::anonymous_fns_alpha_equal;

pub struct ReduceProductBuiltinRuleProof;
pub fn reduce_product(fact: &EqualFact) -> Option<ReduceProductBuiltinRuleProof> {
    for (left, right) in [(&fact.left, &fact.right), (&fact.right, &fact.left)] {
        let (
            Obj::IteratedOperator(IteratedOperator::Reduce(r)),
            Obj::IteratedOperator(IteratedOperator::Product(p)),
        ) = (left, right)
        else {
            continue;
        };
        if !matches!(&*r.seed,Obj::Literal(Literal::Number(n)) if n.normalized_value=="1")
            || r.start.ir() != p.start.ir()
            || r.end.ir() != p.end.ir()
        {
            continue;
        }
        let Obj::FunctionSpace(FunctionSpace::AnonymousFn(op)) = &*r.op else {
            continue;
        };
        let ids: Vec<_> = op
            .body
            .set_bound_parameters
            .groups
            .iter()
            .flat_map(|g| g.params.iter().map(|p| p.id))
            .collect();
        let Obj::ArithmeticOperator(ArithmeticOperator::Mul(m)) = &*op.equal_to else {
            continue;
        };
        let (
            Obj::Identifier(IdentifierObj::Plain { id: a, .. }),
            Obj::Identifier(IdentifierObj::Plain { id: b, .. }),
        ) = (&*m.left, &*m.right)
        else {
            continue;
        };
        if ids.len() != 2 || !((*a == ids[0] && *b == ids[1]) || (*a == ids[1] && *b == ids[0])) {
            continue;
        }
        let functions_match = r.func.ir() == p.func.ir()
            || match (&*r.func, &*p.func) {
                (
                    Obj::FunctionSpace(FunctionSpace::AnonymousFn(a)),
                    Obj::FunctionSpace(FunctionSpace::AnonymousFn(b)),
                ) => anonymous_fns_alpha_equal(a, b),
                _ => false,
            };
        if functions_match {
            return Some(ReduceProductBuiltinRuleProof);
        }
    }
    None
}
