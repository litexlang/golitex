//! Membership contracts: defining clauses, callable carriers and coordinates.
use super::helper::*;
use crate::ast::fact::*;
use crate::ast::obj::*;
use crate::ast::param::*;
use crate::builtin_theorem::BuiltinTheoremId;
use crate::runtime::{Runtime, RuntimeResult};
use std::collections::HashMap;

pub(super) fn prepare_membership(rt: &mut Runtime, id: BuiltinTheoremId, args: &[Obj]) -> RuntimeResult<Result<(Vec<Fact>, Vec<Fact>), String>> {
    use BuiltinTheoremId::*;
    let a = args[0].clone();
    if matches!(id, IndexCartesianNonemptyByChoiceFromFamily | IndexCartesianNonemptyByChoiceFromPointwise) {
        let Obj::SetOperator(SetOperator::IndexCart(cart)) = &a else { return Ok(Err("argument must be index_cart(...)".to_string())); };
        let x = rt.fresh_internal_param();
        let (domain, factor) = if id == IndexCartesianNonemptyByChoiceFromFamily {
            (cart.family_set.as_ref().clone(), identifier(&x))
        } else {
            let factor = match apply(&cart.family_fn, vec![identifier(&x)]) { Ok(x) => x, Err(e) => return Ok(Err(e)) };
            (cart.index_set.as_ref().clone(), factor)
        };
        let body = nonempty(rt, factor);
        let requirement = forall(rt, x, domain, vec![], vec![body]);
        return Ok(Ok((vec![requirement], vec![nonempty(rt, a).into()])));
    }
    let b = args[1].clone();
    let conclusion = if id == TupleEqualFromCoordinates { equal(rt, a.clone(), b.clone()) } else { atomic_in(rt, a.clone(), b.clone()) };
    let requirements = match id {
        FunctionSetMember => {
            let target = match &b {
                Obj::FunctionSpace(FunctionSpace::FnSet(fs)) => fs.clone(),
                Obj::SetFormer(SetFormer::SeqSet(fs)) => as_fn_set(rt, Obj::StandardSet(StandardSet::NPos), fs.set.as_ref().clone()),
                Obj::SetFormer(SetFormer::FiniteSeqSet(fs)) => as_fn_set(rt, range(number("1"), fs.n.as_ref().clone()), fs.set.as_ref().clone()),
                _ => return Ok(Err("second argument must be a function or sequence set".to_string())),
            };
            let mut groups = vec![];
            let mut arguments = vec![];
            for group in &target.set_bound_parameters.groups {
                groups.push(TypedParameterGroup { params: group.params.clone(), param_type: ParamType::Obj(group.param_type.as_ref().clone()) });
                arguments.extend(group.params.iter().map(identifier));
            }
            let value = match apply(&a, arguments) { Ok(x) => x, Err(e) => return Ok(Err(e)) };
            let body = atomic_in(rt, value, target.ret_set.as_ref().clone());
            vec![Fact::ForallFact(ForallFact { fact_id: rt.global_ids.allocate_fact_id(), typed_parameters: TypedParameterList { groups }, dom_facts: target.dom_facts.into_iter().map(crate::instantiate::quantifier_free_fact_to_fact).collect(), then_facts: vec![ExistOrAndChainAtomicFact::AtomicFact(body)], line_file: None })]
        }
        SetBuilderMember => {
            let Obj::SetFormer(SetFormer::SetBuilder(builder)) = &b else { return Ok(Err("second argument must be a set builder".to_string())); };
            let mut requirements = vec![atomic_in(rt, a.clone(), builder.param_set.as_ref().clone()).into()];
            let mut subst = HashMap::new();
            subst.insert(builder.param_binding.id, a);
            for fact in &builder.facts {
                let fact = match rt.inst_quantifier_free_fact(fact, &subst) { Ok(fact) => fact, Err(error) => return Ok(Err(error.to_string())) };
                requirements.push(crate::instantiate::quantifier_free_fact_to_fact(fact));
            }
            requirements
        }
        DefinedSetMember => {
            if !matches!(b, Obj::Identifier(_) | Obj::InstantiatedTemplateObj(_)) { return Ok(Err("second argument must be a named or instantiated defined set".to_string())); }
            // The existing object-definition owner provides the checked unfolding
            // proof. Do not certify an arbitrary set just because it has a name.
            vec![conclusion.clone().into()]
        }
        StructMember => {
            if !matches!(b, Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::StructObj(_))) { return Ok(Err("second argument must be a struct object".to_string())); }
            vec![conclusion.clone().into()]
        }
        CartesianMemberFromCoordinates => cart_requirements(rt, a, b),
        IndexCartesianMember => {
            let Obj::SetOperator(SetOperator::IndexCart(cart)) = &b else { return Ok(Err("second argument must be index_cart(...)".to_string())); };
            let carrier = Obj::SetOperator(SetOperator::FamilyUnion(FamilyUnion { left: cart.family_set.clone() }));
            let fn_set = unary_fn(rt, cart.index_set.as_ref().clone(), carrier);
            let choice: AtomicFact = IsChoiceFunctionForFact { fact_id: rt.global_ids.allocate_fact_id(), index: cart.index_set.as_ref().clone(), set: cart.family_set.as_ref().clone(), family: cart.family_fn.as_ref().clone(), choice: a.clone(), line_file: None }.into();
            vec![atomic_in(rt, a, fn_set).into(), choice.into()]
        }
        TupleEqualFromCoordinates => tuple_requirements(rt, a, b),
        _ => unreachable!(),
    };
    Ok(Ok((requirements, vec![conclusion.into()])))
}

fn as_fn_set(rt: &mut Runtime, domain: Obj, ret: Obj) -> FnSet {
    let Obj::FunctionSpace(FunctionSpace::FnSet(fs)) = unary_fn(rt, domain, ret) else { unreachable!() };
    fs
}
fn tuple_dim(obj: Obj) -> Obj { Obj::ProductShape(ProductShape::TupleDim(TupleDim { arg: Box::new(obj) })) }
fn at(obj: Obj, index: Obj) -> Obj { Obj::ProductShape(ProductShape::ObjAtIndex(ObjAtIndex { obj: Box::new(obj), index: Box::new(index) })) }
fn tuple_requirements(rt: &mut Runtime, a: Obj, b: Obj) -> Vec<Fact> {
    let left: AtomicFact = IsTupleFact { fact_id: rt.global_ids.allocate_fact_id(), set: a.clone(), line_file: None }.into();
    let right: AtomicFact = IsTupleFact { fact_id: rt.global_ids.allocate_fact_id(), set: b.clone(), line_file: None }.into();
    let dimension = tuple_dim(a.clone());
    let mut requirements = vec![left.into(), right.into(), equal(rt, dimension.clone(), tuple_dim(b.clone())).into(), le(rt, number("1"), dimension.clone()).into()];
    if let (Obj::ProductShape(ProductShape::Tuple(left)), Obj::ProductShape(ProductShape::Tuple(right))) = (&a, &b) {
        for (left, right) in left.args.iter().zip(&right.args) {
            requirements.push(equal(rt, left.as_ref().clone(), right.as_ref().clone()).into());
        }
    } else {
        let i = rt.fresh_internal_param();
        let bound = le(rt, identifier(&i), dimension).into();
        let body = equal(rt, at(a, identifier(&i)), at(b, identifier(&i)));
        requirements.push(forall(rt, i, Obj::StandardSet(StandardSet::NPos), vec![bound], vec![body]));
    }
    requirements
}
fn cart_requirements(rt: &mut Runtime, a: Obj, b: Obj) -> Vec<Fact> {
    let tuple: AtomicFact = IsTupleFact { fact_id: rt.global_ids.allocate_fact_id(), set: a.clone(), line_file: None }.into();
    let cart: AtomicFact = IsCartFact { fact_id: rt.global_ids.allocate_fact_id(), set: b.clone(), line_file: None }.into();
    let dimension = Obj::ProductShape(ProductShape::CartDim(CartDim { set: Box::new(b.clone()) }));
    let mut requirements = vec![tuple.into(), cart.into(), equal(rt, tuple_dim(a.clone()), dimension.clone()).into()];
    if let Obj::ProductShape(ProductShape::Cart(cart)) = &b {
        for (index, factor) in cart.args.iter().enumerate() {
            let coordinate = match &a {
                Obj::ProductShape(ProductShape::Tuple(tuple)) => tuple.args.get(index).map(|x| x.as_ref().clone()).unwrap_or_else(|| at(a.clone(), number(&(index + 1).to_string()))),
                _ => at(a.clone(), number(&(index + 1).to_string())),
            };
            requirements.push(atomic_in(rt, coordinate, factor.as_ref().clone()).into());
        }
    } else {
        let i = rt.fresh_internal_param();
        let factor = Obj::ProductShape(ProductShape::Proj(Proj { set: Box::new(b), dim: Box::new(identifier(&i)) }));
        let body = atomic_in(rt, at(a, identifier(&i)), factor);
        requirements.push(forall(rt, i, range(number("1"), dimension), vec![], vec![body]));
    }
    requirements
}
