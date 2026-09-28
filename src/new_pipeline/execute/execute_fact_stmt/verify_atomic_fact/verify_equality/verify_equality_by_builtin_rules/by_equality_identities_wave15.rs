//! Stage B wave 15: finite-set nested-sum Fubini / Cartesian flatten.
//!
//! One matcher ↔ one dedicated proof struct.

use crate::new_pipeline::ast::fact::EqualFact;
use crate::new_pipeline::ast::names::BoundName;
use crate::new_pipeline::ast::obj::{
    AnonymousFn, Cart, FnObj, FnObjHead, FunctionSpace, IdentifierObj, IteratedOperator, Obj,
    ProductShape, SumOfFiniteSet, Tuple,
};
use crate::new_pipeline::ast::param::SetBoundParameterList;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::runtime_ids::IdentifierId;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

// Builtin FiniteSetSumFubiniSwap: swap nested finite-set sum order when both
// sides flatten to the same Cartesian summand.
// Mathematical property: ∑_x∈X ∑_y∈Y f(x,y) = ∑_y∈Y ∑_x∈X f(x,y).
// Example:
//   finite_set_sum({1}, fn(x {1}) R {finite_set_sum({2}, fn(y {2}) R {g((x,y))})})
//   = finite_set_sum({2}, fn(y {2}) R {finite_set_sum({1}, fn(x {1}) R {g((x,y))})}).
pub struct FiniteSetSumFubiniSwapBuiltinRuleProof {}

// Builtin FiniteSetSumOverCartesianProduct: nested double sum equals flat sum
// over the Cartesian product.
// Mathematical property: ∑_x∈X ∑_y∈Y f((x,y)) = ∑_p∈cart(X,Y) f(p).
// Example:
//   finite_set_sum({1}, fn(x {1}) R {finite_set_sum({2}, fn(y {2}) R {g((x,y))})})
//   = finite_set_sum(cart({1}, {2}), g).
pub struct FiniteSetSumOverCartesianProductBuiltinRuleProof {}

pub enum EqualityIdentitiesWave15BuiltinRuleProof {
    FiniteSetSumFubiniSwap(FiniteSetSumFubiniSwapBuiltinRuleProof),
    FiniteSetSumOverCartesianProduct(FiniteSetSumOverCartesianProductBuiltinRuleProof),
}

struct NestedFiniteSetSumCartesianShape {
    product_set: Obj,
    function: Obj,
}

impl Runtime {
    pub fn search_equal_fact_builtin_rule_equality_identities_wave15(
        &mut self,
        fact: &EqualFact,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<EqualityIdentitiesWave15BuiltinRuleProof>> {
        for (left, right) in [(&fact.left, &fact.right), (&fact.right, &fact.left)] {
            if let (Some(l), Some(r)) = (
                nested_finite_set_sum_cartesian_shape(left),
                nested_finite_set_sum_cartesian_shape(right),
            ) {
                if l.product_set.ir() == r.product_set.ir() && l.function.ir() == r.function.ir() {
                    return Ok(Some(
                        EqualityIdentitiesWave15BuiltinRuleProof::FiniteSetSumFubiniSwap(
                            FiniteSetSumFubiniSwapBuiltinRuleProof {},
                        ),
                    ));
                }
            }
            if let Some(nested) = nested_finite_set_sum_cartesian_shape(left) {
                if let Some((flat_set, flat_fn)) = match_flat_finite_set_sum(right) {
                    if flat_set.ir() == nested.product_set.ir()
                        && flat_fn.ir() == nested.function.ir()
                    {
                        return Ok(Some(
                            EqualityIdentitiesWave15BuiltinRuleProof::FiniteSetSumOverCartesianProduct(
                                FiniteSetSumOverCartesianProductBuiltinRuleProof {},
                            ),
                        ));
                    }
                }
            }
        }
        Ok(None)
    }
}

fn nested_finite_set_sum_cartesian_shape(obj: &Obj) -> Option<NestedFiniteSetSumCartesianShape> {
    let outer = match_sum_of_finite_set(obj)?;
    let (outer_param, outer_param_set, outer_body) = unary_anonymous_parts(outer.func.as_ref())?;
    if outer_param_set.ir() != outer.set.ir() {
        return None;
    }
    let inner_sum_obj = outer_body;
    let inner = match_sum_of_finite_set(inner_sum_obj)?;
    // Inner index set must not depend on the outer binder.
    if obj_mentions_param_id(inner.set.as_ref(), outer_param.id) {
        return None;
    }
    let (inner_param, inner_param_set, inner_body) = unary_anonymous_parts(inner.func.as_ref())?;
    if inner_param_set.ir() != inner.set.ir() {
        return None;
    }
    let Obj::FnObj(call) = inner_body else {
        return None;
    };
    if call.body.len() != 1 || call.body[0].len() != 1 {
        return None;
    }
    let Obj::ProductShape(ProductShape::Tuple(Tuple { args })) = call.body[0][0].as_ref() else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }
    let first = args[0].as_ref();
    let second = args[1].as_ref();
    let first_outer = is_param_ref(first, &outer_param);
    let second_inner = is_param_ref(second, &inner_param);
    let first_inner = is_param_ref(first, &inner_param);
    let second_outer = is_param_ref(second, &outer_param);
    let product_set = if first_outer && second_inner {
        cart_of(outer.set.as_ref(), inner.set.as_ref())
    } else if first_inner && second_outer {
        cart_of(inner.set.as_ref(), outer.set.as_ref())
    } else {
        return None;
    };
    let function = callable_head_obj(call.head.as_ref())?;
    Some(NestedFiniteSetSumCartesianShape {
        product_set,
        function,
    })
}

fn match_flat_finite_set_sum(obj: &Obj) -> Option<(&Obj, Obj)> {
    let sum = match_sum_of_finite_set(obj)?;
    let function = match sum.func.as_ref() {
        Obj::Identifier(id) => Obj::Identifier(id.clone()),
        Obj::FnObj(fo) if fo.body.is_empty() => callable_head_obj(fo.head.as_ref())?,
        other => other.clone(),
    };
    Some((sum.set.as_ref(), function))
}

fn match_sum_of_finite_set(obj: &Obj) -> Option<&SumOfFiniteSet> {
    match obj {
        Obj::IteratedOperator(IteratedOperator::SumOfFiniteSet(s)) => Some(s),
        _ => None,
    }
}

fn unary_anonymous_parts(func: &Obj) -> Option<(&BoundName, &Obj, &Obj)> {
    let af = as_unary_anonymous_fn(func)?;
    let (param, param_set) = single_param_and_set(&af.body.set_bound_parameters)?;
    Some((param, param_set, af.equal_to.as_ref()))
}

fn as_unary_anonymous_fn(func: &Obj) -> Option<&AnonymousFn> {
    match func {
        Obj::FunctionSpace(FunctionSpace::AnonymousFn(af)) => Some(af),
        Obj::FnObj(fo) => {
            if !fo.body.is_empty() {
                return None;
            }
            match fo.head.as_ref() {
                FnObjHead::AnonymousFnLiteral(a) => Some(a.as_ref()),
                _ => None,
            }
        }
        _ => None,
    }
}

fn single_param_and_set(list: &SetBoundParameterList) -> Option<(&BoundName, &Obj)> {
    if list.groups.len() != 1 {
        return None;
    }
    let g = &list.groups[0];
    if g.params.len() != 1 {
        return None;
    }
    Some((&g.params[0], g.param_type.as_ref()))
}

fn is_param_ref(obj: &Obj, param: &BoundName) -> bool {
    matches!(
        obj,
        Obj::Identifier(IdentifierObj::Plain { id, name })
            if *id == param.id && *name == param.name
    )
}

fn obj_mentions_param_id(obj: &Obj, id: IdentifierId) -> bool {
    match obj {
        Obj::Identifier(IdentifierObj::Plain { id: oid, .. }) => *oid == id,
        Obj::FnObj(fo) => {
            fo.body
                .iter()
                .flat_map(|g| g.iter())
                .any(|a| obj_mentions_param_id(a.as_ref(), id))
                || match fo.head.as_ref() {
                    FnObjHead::AnonymousFnLiteral(a) => {
                        obj_mentions_param_id(a.equal_to.as_ref(), id)
                    }
                    _ => false,
                }
        }
        Obj::FunctionSpace(FunctionSpace::AnonymousFn(af)) => {
            obj_mentions_param_id(af.equal_to.as_ref(), id)
        }
        Obj::IteratedOperator(IteratedOperator::SumOfFiniteSet(s)) => {
            obj_mentions_param_id(s.set.as_ref(), id)
                || obj_mentions_param_id(s.func.as_ref(), id)
        }
        Obj::ProductShape(ProductShape::Cart(Cart { args }))
        | Obj::ProductShape(ProductShape::Tuple(Tuple { args })) => {
            args.iter().any(|a| obj_mentions_param_id(a.as_ref(), id))
        }
        _ => false,
    }
}

fn cart_of(left: &Obj, right: &Obj) -> Obj {
    Obj::ProductShape(ProductShape::Cart(Cart {
        args: vec![Box::new(left.clone()), Box::new(right.clone())],
    }))
}

fn callable_head_obj(head: &FnObjHead) -> Option<Obj> {
    match head {
        FnObjHead::Identifier(id) => Some(Obj::Identifier(id.clone())),
        FnObjHead::InstantiatedTemplateObj(t) => Some(Obj::InstantiatedTemplateObj(t.clone())),
        FnObjHead::FieldAccess(f) => Some(Obj::StructAndFieldAccessObj(
            crate::new_pipeline::ast::obj::StructAndFieldAccessObj::FieldAccess(f.clone()),
        )),
        FnObjHead::AnonymousFnLiteral(_) => None,
    }
}
