use crate::new_pipeline::ast::obj::{
    BigIntersect, BigUnion, Cart, CartDim, ClosedRange, FiniteSeqListObj, FiniteSeqSet, FiniteSetMax,
    FiniteSetMin, FiniteSetReduce, FiniteSetSize, FnRange, GeneralCart, IndexIntersect, IndexUnion,
    Intersect, ListSet, Obj, PowerSet, Product, ProductOfFiniteSet, Proj, Range, Reduce,
    Replacement, SeqSet, SetMinus, Sum, SumOfFiniteSet, Tuple, TupleDim, Union,
};

use super::super::InstCtx;
use super::super::error::InstError;

pub fn inst_union(ctx: &mut InstCtx<'_>, a: &Union) -> Result<Obj, InstError> {
    Ok(Obj::Union(Union {
        left: Box::new(ctx.inst_obj(&a.left)?),
        right: Box::new(ctx.inst_obj(&a.right)?),
    }))
}

pub fn inst_intersect(ctx: &mut InstCtx<'_>, a: &Intersect) -> Result<Obj, InstError> {
    Ok(Obj::Intersect(Intersect {
        left: Box::new(ctx.inst_obj(&a.left)?),
        right: Box::new(ctx.inst_obj(&a.right)?),
    }))
}

pub fn inst_set_minus(ctx: &mut InstCtx<'_>, a: &SetMinus) -> Result<Obj, InstError> {
    Ok(Obj::SetMinus(SetMinus {
        left: Box::new(ctx.inst_obj(&a.left)?),
        right: Box::new(ctx.inst_obj(&a.right)?),
    }))
}

pub fn inst_big_union(ctx: &mut InstCtx<'_>, a: &BigUnion) -> Result<Obj, InstError> {
    Ok(Obj::BigUnion(BigUnion {
        left: Box::new(ctx.inst_obj(&a.left)?),
    }))
}

pub fn inst_big_intersect(ctx: &mut InstCtx<'_>, a: &BigIntersect) -> Result<Obj, InstError> {
    Ok(Obj::BigIntersect(BigIntersect {
        left: Box::new(ctx.inst_obj(&a.left)?),
    }))
}

pub fn inst_index_union(ctx: &mut InstCtx<'_>, a: &IndexUnion) -> Result<Obj, InstError> {
    Ok(Obj::IndexUnion(IndexUnion {
        index_set: Box::new(ctx.inst_obj(&a.index_set)?),
        ambient_set: Box::new(ctx.inst_obj(&a.ambient_set)?),
        family_fn: Box::new(ctx.inst_obj(&a.family_fn)?),
    }))
}

pub fn inst_index_intersect(ctx: &mut InstCtx<'_>, a: &IndexIntersect) -> Result<Obj, InstError> {
    Ok(Obj::IndexIntersect(IndexIntersect {
        index_set: Box::new(ctx.inst_obj(&a.index_set)?),
        ambient_set: Box::new(ctx.inst_obj(&a.ambient_set)?),
        family_fn: Box::new(ctx.inst_obj(&a.family_fn)?),
    }))
}

pub fn inst_power_set(ctx: &mut InstCtx<'_>, a: &PowerSet) -> Result<Obj, InstError> {
    Ok(Obj::PowerSet(PowerSet {
        set: Box::new(ctx.inst_obj(&a.set)?),
    }))
}

pub fn inst_general_cart(ctx: &mut InstCtx<'_>, a: &GeneralCart) -> Result<Obj, InstError> {
    Ok(Obj::GeneralCart(GeneralCart {
        index_set: Box::new(ctx.inst_obj(&a.index_set)?),
        family_set: Box::new(ctx.inst_obj(&a.family_set)?),
        family_fn: Box::new(ctx.inst_obj(&a.family_fn)?),
    }))
}

pub fn inst_list_set(ctx: &mut InstCtx<'_>, a: &ListSet) -> Result<Obj, InstError> {
    let mut list = Vec::with_capacity(a.list.len());
    for o in &a.list {
        list.push(Box::new(ctx.inst_obj(o)?));
    }
    Ok(Obj::ListSet(ListSet { list }))
}

pub fn inst_cart(ctx: &mut InstCtx<'_>, a: &Cart) -> Result<Obj, InstError> {
    let mut args = Vec::with_capacity(a.args.len());
    for o in &a.args {
        args.push(Box::new(ctx.inst_obj(o)?));
    }
    Ok(Obj::Cart(Cart { args }))
}

pub fn inst_tuple(ctx: &mut InstCtx<'_>, a: &Tuple) -> Result<Obj, InstError> {
    let mut args = Vec::with_capacity(a.args.len());
    for o in &a.args {
        args.push(Box::new(ctx.inst_obj(o)?));
    }
    Ok(Obj::Tuple(Tuple { args }))
}

pub fn inst_cart_dim(ctx: &mut InstCtx<'_>, a: &CartDim) -> Result<Obj, InstError> {
    Ok(Obj::CartDim(CartDim {
        set: Box::new(ctx.inst_obj(&a.set)?),
    }))
}

pub fn inst_proj(ctx: &mut InstCtx<'_>, a: &Proj) -> Result<Obj, InstError> {
    Ok(Obj::Proj(Proj {
        set: Box::new(ctx.inst_obj(&a.set)?),
        dim: Box::new(ctx.inst_obj(&a.dim)?),
    }))
}

pub fn inst_tuple_dim(ctx: &mut InstCtx<'_>, a: &TupleDim) -> Result<Obj, InstError> {
    Ok(Obj::TupleDim(TupleDim {
        arg: Box::new(ctx.inst_obj(&a.arg)?),
    }))
}

pub fn inst_finite_set_size(ctx: &mut InstCtx<'_>, a: &FiniteSetSize) -> Result<Obj, InstError> {
    Ok(Obj::FiniteSetSize(FiniteSetSize {
        set: Box::new(ctx.inst_obj(&a.set)?),
    }))
}

pub fn inst_finite_set_max(ctx: &mut InstCtx<'_>, a: &FiniteSetMax) -> Result<Obj, InstError> {
    Ok(Obj::FiniteSetMax(FiniteSetMax {
        set: Box::new(ctx.inst_obj(&a.set)?),
    }))
}

pub fn inst_finite_set_min(ctx: &mut InstCtx<'_>, a: &FiniteSetMin) -> Result<Obj, InstError> {
    Ok(Obj::FiniteSetMin(FiniteSetMin {
        set: Box::new(ctx.inst_obj(&a.set)?),
    }))
}

pub fn inst_fn_range(ctx: &mut InstCtx<'_>, a: &FnRange) -> Result<Obj, InstError> {
    Ok(Obj::FnRange(FnRange {
        function: Box::new(ctx.inst_obj(&a.function)?),
    }))
}

pub fn inst_replacement(ctx: &mut InstCtx<'_>, a: &Replacement) -> Result<Obj, InstError> {
    Ok(Obj::Replacement(Replacement {
        prop_name: a.prop_name.clone(),
        source_set: Box::new(ctx.inst_obj(&a.source_set)?),
    }))
}

pub fn inst_sum(ctx: &mut InstCtx<'_>, a: &Sum) -> Result<Obj, InstError> {
    Ok(Obj::Sum(Sum {
        start: Box::new(ctx.inst_obj(&a.start)?),
        end: Box::new(ctx.inst_obj(&a.end)?),
        func: Box::new(ctx.inst_obj(&a.func)?),
    }))
}

pub fn inst_sum_of_finite_set(ctx: &mut InstCtx<'_>, a: &SumOfFiniteSet) -> Result<Obj, InstError> {
    Ok(Obj::SumOfFiniteSet(SumOfFiniteSet {
        set: Box::new(ctx.inst_obj(&a.set)?),
        func: Box::new(ctx.inst_obj(&a.func)?),
    }))
}

pub fn inst_product(ctx: &mut InstCtx<'_>, a: &Product) -> Result<Obj, InstError> {
    Ok(Obj::Product(Product {
        start: Box::new(ctx.inst_obj(&a.start)?),
        end: Box::new(ctx.inst_obj(&a.end)?),
        func: Box::new(ctx.inst_obj(&a.func)?),
    }))
}

pub fn inst_product_of_finite_set(
    ctx: &mut InstCtx<'_>,
    a: &ProductOfFiniteSet,
) -> Result<Obj, InstError> {
    Ok(Obj::ProductOfFiniteSet(ProductOfFiniteSet {
        set: Box::new(ctx.inst_obj(&a.set)?),
        func: Box::new(ctx.inst_obj(&a.func)?),
    }))
}

pub fn inst_reduce(ctx: &mut InstCtx<'_>, a: &Reduce) -> Result<Obj, InstError> {
    Ok(Obj::Reduce(Reduce {
        start: Box::new(ctx.inst_obj(&a.start)?),
        end: Box::new(ctx.inst_obj(&a.end)?),
        func: Box::new(ctx.inst_obj(&a.func)?),
        op: Box::new(ctx.inst_obj(&a.op)?),
        seed: Box::new(ctx.inst_obj(&a.seed)?),
    }))
}

pub fn inst_finite_set_reduce(ctx: &mut InstCtx<'_>, a: &FiniteSetReduce) -> Result<Obj, InstError> {
    Ok(Obj::FiniteSetReduce(FiniteSetReduce {
        set: Box::new(ctx.inst_obj(&a.set)?),
        func: Box::new(ctx.inst_obj(&a.func)?),
        op: Box::new(ctx.inst_obj(&a.op)?),
        seed: Box::new(ctx.inst_obj(&a.seed)?),
    }))
}

pub fn inst_range(ctx: &mut InstCtx<'_>, a: &Range) -> Result<Obj, InstError> {
    Ok(Obj::Range(Range {
        start: Box::new(ctx.inst_obj(&a.start)?),
        end: Box::new(ctx.inst_obj(&a.end)?),
    }))
}

pub fn inst_closed_range(ctx: &mut InstCtx<'_>, a: &ClosedRange) -> Result<Obj, InstError> {
    Ok(Obj::ClosedRange(ClosedRange {
        start: Box::new(ctx.inst_obj(&a.start)?),
        end: Box::new(ctx.inst_obj(&a.end)?),
    }))
}

pub fn inst_finite_seq_set(ctx: &mut InstCtx<'_>, a: &FiniteSeqSet) -> Result<Obj, InstError> {
    Ok(Obj::FiniteSeqSet(FiniteSeqSet {
        set: Box::new(ctx.inst_obj(&a.set)?),
        n: Box::new(ctx.inst_obj(&a.n)?),
    }))
}

pub fn inst_seq_set(ctx: &mut InstCtx<'_>, a: &SeqSet) -> Result<Obj, InstError> {
    Ok(Obj::SeqSet(SeqSet {
        set: Box::new(ctx.inst_obj(&a.set)?),
    }))
}

pub fn inst_finite_seq_list_obj(ctx: &mut InstCtx<'_>, a: &FiniteSeqListObj) -> Result<Obj, InstError> {
    let mut objs = Vec::with_capacity(a.objs.len());
    for o in &a.objs {
        objs.push(Box::new(ctx.inst_obj(o)?));
    }
    Ok(Obj::FiniteSeqListObj(FiniteSeqListObj { objs }))
}

pub fn inst_obj_at_index(
    ctx: &mut InstCtx<'_>,
    a: &crate::new_pipeline::ast::obj::ObjAtIndex,
) -> Result<Obj, InstError> {
    Ok(Obj::ObjAtIndex(crate::new_pipeline::ast::obj::ObjAtIndex {
        obj: Box::new(ctx.inst_obj(&a.obj)?),
        index: Box::new(ctx.inst_obj(&a.index)?),
    }))
}
