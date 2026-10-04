//! Explicit defining equation for an unordered fold over one element.
use super::helper::{apply, equal};
use crate::ast::fact::Fact;
use crate::ast::obj::{IteratedOperator, ListSet, Obj, SetFormer};
use crate::runtime::Runtime;

pub(super) fn prepare_singleton(
    rt: &mut Runtime,
    args: &[Obj],
) -> Result<(Vec<Fact>, Vec<Fact>), String> {
    let Obj::IteratedOperator(IteratedOperator::FiniteSetReduce(reduction)) = &args[0] else {
        return Err("first argument must be finite_set_reduce(...)".to_string());
    };
    let element = args[1].clone();
    let singleton = Obj::SetFormer(SetFormer::ListSet(ListSet {
        list: vec![Box::new(element.clone())],
    }));
    let requirement: Fact = equal(rt, reduction.set.as_ref().clone(), singleton).into();
    let term = apply_fold(&reduction.func, vec![element])?;
    let value = apply_fold(&reduction.op, vec![reduction.seed.as_ref().clone(), term])?;
    // S={x} gives fold(S,f,op,seed)=op(seed,f(x)). The ordinary release
    // executor checks the whole conclusion's WD before publishing it, including
    // the fold's homogeneous carrier, seed, and associative/commutative laws.
    // Example: release thm finite_set_reduce_singleton(finite_set_reduce({2},
    // fn(x Z) Z{x}, fn(a,b Z) Z{a+b}, 0), 2).
    Ok((vec![requirement], vec![equal(rt, args[0].clone(), value).into()]))
}

fn apply_fold(function: &Obj, arguments: Vec<Obj>) -> Result<Obj, String> {
    if let Obj::FnObj(existing) = function {
        let mut application = existing.clone();
        application.body.push(arguments.into_iter().map(Box::new).collect());
        Ok(Obj::FnObj(application))
    } else {
        apply(function, arguments)
    }
}
