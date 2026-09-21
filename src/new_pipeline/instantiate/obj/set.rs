use std::collections::HashMap;

use crate::new_pipeline::runtime::runtime_ids::IdentifierId;

use crate::new_pipeline::ast::obj::{
    BigIntersect, BigUnion, Cart, CartDim, ClosedRange, FiniteSeqSet, FiniteSetMax,
    FiniteSetMin, FiniteSetReduce, FiniteSetSize, FnRange, GeneralCart, IndexIntersect, IndexUnion,
    Intersect, ListSet, Obj, PowerSet, Product, ProductOfFiniteSet, Proj, Range, Reduce,
    Replacement, SeqSet, SetMinus, Sum, SumOfFiniteSet, Tuple, TupleDim, Union,
};
use crate::new_pipeline::runtime::Runtime;

use super::super::error::InstError;

impl Runtime {
    pub(crate) fn inst_union_obj(
        &mut self,
        a: &Union,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
    Ok(Obj::Union(Union {
        left: Box::new(self.inst_obj_rec(&a.left, param_to_arg_map)?),
        right: Box::new(self.inst_obj_rec(&a.right, param_to_arg_map)?),
    }))
}


    pub(crate) fn inst_intersect_obj(
        &mut self,
        a: &Intersect,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
    Ok(Obj::Intersect(Intersect {
        left: Box::new(self.inst_obj_rec(&a.left, param_to_arg_map)?),
        right: Box::new(self.inst_obj_rec(&a.right, param_to_arg_map)?),
    }))
}


    pub(crate) fn inst_set_minus_obj(
        &mut self,
        a: &SetMinus,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
    Ok(Obj::SetMinus(SetMinus {
        left: Box::new(self.inst_obj_rec(&a.left, param_to_arg_map)?),
        right: Box::new(self.inst_obj_rec(&a.right, param_to_arg_map)?),
    }))
}


    pub(crate) fn inst_big_union_obj(
        &mut self,
        a: &BigUnion,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
    Ok(Obj::BigUnion(BigUnion {
        left: Box::new(self.inst_obj_rec(&a.left, param_to_arg_map)?),
    }))
}


    pub(crate) fn inst_big_intersect_obj(
        &mut self,
        a: &BigIntersect,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
    Ok(Obj::BigIntersect(BigIntersect {
        left: Box::new(self.inst_obj_rec(&a.left, param_to_arg_map)?),
    }))
}


    pub(crate) fn inst_index_union_obj(
        &mut self,
        a: &IndexUnion,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
    Ok(Obj::IndexUnion(IndexUnion {
        index_set: Box::new(self.inst_obj_rec(&a.index_set, param_to_arg_map)?),
        ambient_set: Box::new(self.inst_obj_rec(&a.ambient_set, param_to_arg_map)?),
        family_fn: Box::new(self.inst_obj_rec(&a.family_fn, param_to_arg_map)?),
    }))
}


    pub(crate) fn inst_index_intersect_obj(
        &mut self,
        a: &IndexIntersect,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
    Ok(Obj::IndexIntersect(IndexIntersect {
        index_set: Box::new(self.inst_obj_rec(&a.index_set, param_to_arg_map)?),
        ambient_set: Box::new(self.inst_obj_rec(&a.ambient_set, param_to_arg_map)?),
        family_fn: Box::new(self.inst_obj_rec(&a.family_fn, param_to_arg_map)?),
    }))
}


    pub(crate) fn inst_power_set_obj(
        &mut self,
        a: &PowerSet,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
    Ok(Obj::PowerSet(PowerSet {
        set: Box::new(self.inst_obj_rec(&a.set, param_to_arg_map)?),
    }))
}


    pub(crate) fn inst_general_cart_obj(
        &mut self,
        a: &GeneralCart,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
    Ok(Obj::GeneralCart(GeneralCart {
        index_set: Box::new(self.inst_obj_rec(&a.index_set, param_to_arg_map)?),
        family_set: Box::new(self.inst_obj_rec(&a.family_set, param_to_arg_map)?),
        family_fn: Box::new(self.inst_obj_rec(&a.family_fn, param_to_arg_map)?),
    }))
}


    pub(crate) fn inst_list_set_obj(
        &mut self,
        a: &ListSet,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
    let mut list = Vec::with_capacity(a.list.len());
    for o in &a.list {
        list.push(Box::new(self.inst_obj_rec(o, param_to_arg_map)?));
    }
    Ok(Obj::ListSet(ListSet { list }))
}


    pub(crate) fn inst_cart_obj(
        &mut self,
        a: &Cart,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
    let mut args = Vec::with_capacity(a.args.len());
    for o in &a.args {
        args.push(Box::new(self.inst_obj_rec(o, param_to_arg_map)?));
    }
    Ok(Obj::Cart(Cart { args }))
}


    pub(crate) fn inst_tuple_obj(
        &mut self,
        a: &Tuple,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
    let mut args = Vec::with_capacity(a.args.len());
    for o in &a.args {
        args.push(Box::new(self.inst_obj_rec(o, param_to_arg_map)?));
    }
    Ok(Obj::Tuple(Tuple { args }))
}


    pub(crate) fn inst_cart_dim_obj(
        &mut self,
        a: &CartDim,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
    Ok(Obj::CartDim(CartDim {
        set: Box::new(self.inst_obj_rec(&a.set, param_to_arg_map)?),
    }))
}


    pub(crate) fn inst_proj_obj(
        &mut self,
        a: &Proj,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
    Ok(Obj::Proj(Proj {
        set: Box::new(self.inst_obj_rec(&a.set, param_to_arg_map)?),
        dim: Box::new(self.inst_obj_rec(&a.dim, param_to_arg_map)?),
    }))
}


    pub(crate) fn inst_tuple_dim_obj(
        &mut self,
        a: &TupleDim,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
    Ok(Obj::TupleDim(TupleDim {
        arg: Box::new(self.inst_obj_rec(&a.arg, param_to_arg_map)?),
    }))
}


    pub(crate) fn inst_finite_set_size_obj(
        &mut self,
        a: &FiniteSetSize,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
    Ok(Obj::FiniteSetSize(FiniteSetSize {
        set: Box::new(self.inst_obj_rec(&a.set, param_to_arg_map)?),
    }))
}


    pub(crate) fn inst_finite_set_max_obj(
        &mut self,
        a: &FiniteSetMax,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
    Ok(Obj::FiniteSetMax(FiniteSetMax {
        set: Box::new(self.inst_obj_rec(&a.set, param_to_arg_map)?),
    }))
}


    pub(crate) fn inst_finite_set_min_obj(
        &mut self,
        a: &FiniteSetMin,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
    Ok(Obj::FiniteSetMin(FiniteSetMin {
        set: Box::new(self.inst_obj_rec(&a.set, param_to_arg_map)?),
    }))
}


    pub(crate) fn inst_fn_range_obj(
        &mut self,
        a: &FnRange,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
    Ok(Obj::FnRange(FnRange {
        function: Box::new(self.inst_obj_rec(&a.function, param_to_arg_map)?),
    }))
}


    pub(crate) fn inst_replacement_obj(
        &mut self,
        a: &Replacement,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
    Ok(Obj::Replacement(Replacement {
        prop_name: a.prop_name.clone(),
        source_set: Box::new(self.inst_obj_rec(&a.source_set, param_to_arg_map)?),
    }))
}


    pub(crate) fn inst_sum_obj(
        &mut self,
        a: &Sum,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
    Ok(Obj::Sum(Sum {
        start: Box::new(self.inst_obj_rec(&a.start, param_to_arg_map)?),
        end: Box::new(self.inst_obj_rec(&a.end, param_to_arg_map)?),
        func: Box::new(self.inst_obj_rec(&a.func, param_to_arg_map)?),
    }))
}


    pub(crate) fn inst_sum_of_finite_set_obj(
        &mut self,
        a: &SumOfFiniteSet,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
    Ok(Obj::SumOfFiniteSet(SumOfFiniteSet {
        set: Box::new(self.inst_obj_rec(&a.set, param_to_arg_map)?),
        func: Box::new(self.inst_obj_rec(&a.func, param_to_arg_map)?),
    }))
}


    pub(crate) fn inst_product_obj(
        &mut self,
        a: &Product,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
    Ok(Obj::Product(Product {
        start: Box::new(self.inst_obj_rec(&a.start, param_to_arg_map)?),
        end: Box::new(self.inst_obj_rec(&a.end, param_to_arg_map)?),
        func: Box::new(self.inst_obj_rec(&a.func, param_to_arg_map)?),
    }))
}


    pub(crate) fn inst_product_of_finite_set_obj(
        &mut self,
        a: &ProductOfFiniteSet,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
    Ok(Obj::ProductOfFiniteSet(ProductOfFiniteSet {
        set: Box::new(self.inst_obj_rec(&a.set, param_to_arg_map)?),
        func: Box::new(self.inst_obj_rec(&a.func, param_to_arg_map)?),
    }))
}


    pub(crate) fn inst_reduce_obj(
        &mut self,
        a: &Reduce,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
    Ok(Obj::Reduce(Reduce {
        start: Box::new(self.inst_obj_rec(&a.start, param_to_arg_map)?),
        end: Box::new(self.inst_obj_rec(&a.end, param_to_arg_map)?),
        func: Box::new(self.inst_obj_rec(&a.func, param_to_arg_map)?),
        op: Box::new(self.inst_obj_rec(&a.op, param_to_arg_map)?),
        seed: Box::new(self.inst_obj_rec(&a.seed, param_to_arg_map)?),
    }))
}


    pub(crate) fn inst_finite_set_reduce_obj(
        &mut self,
        a: &FiniteSetReduce,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
    Ok(Obj::FiniteSetReduce(FiniteSetReduce {
        set: Box::new(self.inst_obj_rec(&a.set, param_to_arg_map)?),
        func: Box::new(self.inst_obj_rec(&a.func, param_to_arg_map)?),
        op: Box::new(self.inst_obj_rec(&a.op, param_to_arg_map)?),
        seed: Box::new(self.inst_obj_rec(&a.seed, param_to_arg_map)?),
    }))
}


    pub(crate) fn inst_range_obj(
        &mut self,
        a: &Range,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
    Ok(Obj::Range(Range {
        start: Box::new(self.inst_obj_rec(&a.start, param_to_arg_map)?),
        end: Box::new(self.inst_obj_rec(&a.end, param_to_arg_map)?),
    }))
}


    pub(crate) fn inst_closed_range_obj(
        &mut self,
        a: &ClosedRange,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
    Ok(Obj::ClosedRange(ClosedRange {
        start: Box::new(self.inst_obj_rec(&a.start, param_to_arg_map)?),
        end: Box::new(self.inst_obj_rec(&a.end, param_to_arg_map)?),
    }))
}


    pub(crate) fn inst_finite_seq_set_obj(
        &mut self,
        a: &FiniteSeqSet,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
    Ok(Obj::FiniteSeqSet(FiniteSeqSet {
        set: Box::new(self.inst_obj_rec(&a.set, param_to_arg_map)?),
        n: Box::new(self.inst_obj_rec(&a.n, param_to_arg_map)?),
    }))
}


    pub(crate) fn inst_seq_set_obj(
        &mut self,
        a: &SeqSet,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
    Ok(Obj::SeqSet(SeqSet {
        set: Box::new(self.inst_obj_rec(&a.set, param_to_arg_map)?),
    }))
}


    pub(crate) fn inst_obj_at_index_obj(
        &mut self,
        a: &crate::new_pipeline::ast::obj::ObjAtIndex,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
    Ok(Obj::ObjAtIndex(crate::new_pipeline::ast::obj::ObjAtIndex {
        obj: Box::new(self.inst_obj_rec(&a.obj, param_to_arg_map)?),
        index: Box::new(self.inst_obj_rec(&a.index, param_to_arg_map)?),
    }))
}
}
