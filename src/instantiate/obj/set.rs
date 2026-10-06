use std::collections::HashMap;

use crate::runtime::runtime_ids::IdentifierId;

use crate::ast::obj::{FamilyIntersect, FamilyUnion, Cart, ClosedRange, FiniteSeqSet, FiniteSetMax, FiniteSetMin, FiniteSetReduce, FiniteSetSize, FnRange, IndexCart, IndexIntersect, IndexUnion, Intersect, ListSet, Obj, PowerSet, Product, ProductOfFiniteSet, Range, Reduce, SeqSet, SetMinus, Sum, SumOfFiniteSet, Tuple, Union, FiniteSetStat, FunctionSpace, IteratedOperator, ProductShape, SetFormer, SetOperator};
use crate::runtime::Runtime;

use super::super::error::InstError;

impl Runtime {
    pub(crate) fn inst_union_obj(
        &mut self,
        a: &Union,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
    Ok(Obj::SetOperator(SetOperator::Union(Union {
        left: Box::new(self.inst_obj_rec(&a.left, param_to_arg_map)?),
        right: Box::new(self.inst_obj_rec(&a.right, param_to_arg_map)?),
    })))
}


    pub(crate) fn inst_intersect_obj(
        &mut self,
        a: &Intersect,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
    Ok(Obj::SetOperator(SetOperator::Intersect(Intersect {
        left: Box::new(self.inst_obj_rec(&a.left, param_to_arg_map)?),
        right: Box::new(self.inst_obj_rec(&a.right, param_to_arg_map)?),
    })))
}


    pub(crate) fn inst_set_minus_obj(
        &mut self,
        a: &SetMinus,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
    Ok(Obj::SetOperator(SetOperator::SetMinus(SetMinus {
        left: Box::new(self.inst_obj_rec(&a.left, param_to_arg_map)?),
        right: Box::new(self.inst_obj_rec(&a.right, param_to_arg_map)?),
    })))
}


    pub(crate) fn inst_family_union_obj(
        &mut self,
        a: &FamilyUnion,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
    Ok(Obj::SetOperator(SetOperator::FamilyUnion(FamilyUnion {
        left: Box::new(self.inst_obj_rec(&a.left, param_to_arg_map)?),
    })))
}


    pub(crate) fn inst_family_intersect_obj(
        &mut self,
        a: &FamilyIntersect,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
    Ok(Obj::SetOperator(SetOperator::FamilyIntersect(FamilyIntersect {
        left: Box::new(self.inst_obj_rec(&a.left, param_to_arg_map)?),
    })))
}


    pub(crate) fn inst_index_union_obj(
        &mut self,
        a: &IndexUnion,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
    Ok(Obj::SetOperator(SetOperator::IndexUnion(IndexUnion {
        index_set: Box::new(self.inst_obj_rec(&a.index_set, param_to_arg_map)?),
        ambient_set: Box::new(self.inst_obj_rec(&a.ambient_set, param_to_arg_map)?),
        family_fn: Box::new(self.inst_obj_rec(&a.family_fn, param_to_arg_map)?),
    })))
}


    pub(crate) fn inst_index_intersect_obj(
        &mut self,
        a: &IndexIntersect,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
    Ok(Obj::SetOperator(SetOperator::IndexIntersect(IndexIntersect {
        index_set: Box::new(self.inst_obj_rec(&a.index_set, param_to_arg_map)?),
        ambient_set: Box::new(self.inst_obj_rec(&a.ambient_set, param_to_arg_map)?),
        family_fn: Box::new(self.inst_obj_rec(&a.family_fn, param_to_arg_map)?),
    })))
}


    pub(crate) fn inst_power_set_obj(
        &mut self,
        a: &PowerSet,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
    Ok(Obj::SetOperator(SetOperator::PowerSet(PowerSet {
        set: Box::new(self.inst_obj_rec(&a.set, param_to_arg_map)?),
    })))
}


    pub(crate) fn inst_index_cart_obj(
        &mut self,
        a: &IndexCart,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
    Ok(Obj::SetOperator(SetOperator::IndexCart(IndexCart {
        index_set: Box::new(self.inst_obj_rec(&a.index_set, param_to_arg_map)?),
        family_set: Box::new(self.inst_obj_rec(&a.family_set, param_to_arg_map)?),
        family_fn: Box::new(self.inst_obj_rec(&a.family_fn, param_to_arg_map)?),
    })))
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
    Ok(Obj::SetFormer(SetFormer::ListSet(ListSet { list })))
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
    Ok(Obj::ProductShape(ProductShape::Cart(Cart { args })))
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
    Ok(Obj::ProductShape(ProductShape::Tuple(Tuple { args })))
}



    pub(crate) fn inst_finite_set_size_obj(
        &mut self,
        a: &FiniteSetSize,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
    Ok(Obj::FiniteSetStat(FiniteSetStat::FiniteSetSize(FiniteSetSize {
        set: Box::new(self.inst_obj_rec(&a.set, param_to_arg_map)?),
    })))
}


    pub(crate) fn inst_finite_set_max_obj(
        &mut self,
        a: &FiniteSetMax,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
    Ok(Obj::FiniteSetStat(FiniteSetStat::FiniteSetMax(FiniteSetMax {
        set: Box::new(self.inst_obj_rec(&a.set, param_to_arg_map)?),
    })))
}


    pub(crate) fn inst_finite_set_min_obj(
        &mut self,
        a: &FiniteSetMin,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
    Ok(Obj::FiniteSetStat(FiniteSetStat::FiniteSetMin(FiniteSetMin {
        set: Box::new(self.inst_obj_rec(&a.set, param_to_arg_map)?),
    })))
}


    pub(crate) fn inst_fn_range_obj(
        &mut self,
        a: &FnRange,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
    Ok(Obj::FunctionSpace(FunctionSpace::FnRange(FnRange {
        function: Box::new(self.inst_obj_rec(&a.function, param_to_arg_map)?),
    })))
}


    pub(crate) fn inst_sum_obj(
        &mut self,
        a: &Sum,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
    Ok(Obj::IteratedOperator(IteratedOperator::Sum(Sum {
        start: Box::new(self.inst_obj_rec(&a.start, param_to_arg_map)?),
        end: Box::new(self.inst_obj_rec(&a.end, param_to_arg_map)?),
        func: Box::new(self.inst_obj_rec(&a.func, param_to_arg_map)?),
    })))
}


    pub(crate) fn inst_sum_of_finite_set_obj(
        &mut self,
        a: &SumOfFiniteSet,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
    Ok(Obj::IteratedOperator(IteratedOperator::SumOfFiniteSet(SumOfFiniteSet {
        set: Box::new(self.inst_obj_rec(&a.set, param_to_arg_map)?),
        func: Box::new(self.inst_obj_rec(&a.func, param_to_arg_map)?),
    })))
}


    pub(crate) fn inst_product_obj(
        &mut self,
        a: &Product,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
    Ok(Obj::IteratedOperator(IteratedOperator::Product(Product {
        start: Box::new(self.inst_obj_rec(&a.start, param_to_arg_map)?),
        end: Box::new(self.inst_obj_rec(&a.end, param_to_arg_map)?),
        func: Box::new(self.inst_obj_rec(&a.func, param_to_arg_map)?),
    })))
}


    pub(crate) fn inst_product_of_finite_set_obj(
        &mut self,
        a: &ProductOfFiniteSet,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
    Ok(Obj::IteratedOperator(IteratedOperator::ProductOfFiniteSet(ProductOfFiniteSet {
        set: Box::new(self.inst_obj_rec(&a.set, param_to_arg_map)?),
        func: Box::new(self.inst_obj_rec(&a.func, param_to_arg_map)?),
    })))
}


    pub(crate) fn inst_reduce_obj(
        &mut self,
        a: &Reduce,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
    Ok(Obj::IteratedOperator(IteratedOperator::Reduce(Reduce {
        start: Box::new(self.inst_obj_rec(&a.start, param_to_arg_map)?),
        end: Box::new(self.inst_obj_rec(&a.end, param_to_arg_map)?),
        func: Box::new(self.inst_obj_rec(&a.func, param_to_arg_map)?),
        op: Box::new(self.inst_obj_rec(&a.op, param_to_arg_map)?),
        seed: Box::new(self.inst_obj_rec(&a.seed, param_to_arg_map)?),
    })))
}


    pub(crate) fn inst_finite_set_reduce_obj(
        &mut self,
        a: &FiniteSetReduce,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
    Ok(Obj::IteratedOperator(IteratedOperator::FiniteSetReduce(FiniteSetReduce {
        set: Box::new(self.inst_obj_rec(&a.set, param_to_arg_map)?),
        func: Box::new(self.inst_obj_rec(&a.func, param_to_arg_map)?),
        op: Box::new(self.inst_obj_rec(&a.op, param_to_arg_map)?),
        seed: Box::new(self.inst_obj_rec(&a.seed, param_to_arg_map)?),
    })))
}


    pub(crate) fn inst_range_obj(
        &mut self,
        a: &Range,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
    Ok(Obj::SetFormer(SetFormer::Range(Range {
        start: Box::new(self.inst_obj_rec(&a.start, param_to_arg_map)?),
        end: Box::new(self.inst_obj_rec(&a.end, param_to_arg_map)?),
    })))
}


    pub(crate) fn inst_closed_range_obj(
        &mut self,
        a: &ClosedRange,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
    Ok(Obj::SetFormer(SetFormer::ClosedRange(ClosedRange {
        start: Box::new(self.inst_obj_rec(&a.start, param_to_arg_map)?),
        end: Box::new(self.inst_obj_rec(&a.end, param_to_arg_map)?),
    })))
}


    pub(crate) fn inst_finite_seq_set_obj(
        &mut self,
        a: &FiniteSeqSet,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
    Ok(Obj::SetFormer(SetFormer::FiniteSeqSet(FiniteSeqSet {
        set: Box::new(self.inst_obj_rec(&a.set, param_to_arg_map)?),
        n: Box::new(self.inst_obj_rec(&a.n, param_to_arg_map)?),
    })))
}


    pub(crate) fn inst_seq_set_obj(
        &mut self,
        a: &SeqSet,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,

    ) -> Result<Obj, InstError> {
    Ok(Obj::SetFormer(SetFormer::SeqSet(SeqSet {
        set: Box::new(self.inst_obj_rec(&a.set, param_to_arg_map)?),
    })))
}

}
