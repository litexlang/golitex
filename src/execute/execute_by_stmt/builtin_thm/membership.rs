//! Membership contracts: defining clauses, callable carriers and coordinates.
use super::helper::*;
use crate::ast::fact::*;
use crate::ast::obj::*;
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
            let Some(target) = rt.function_space_signature(&b) else {
                return Ok(Err("second argument must be a function or sequence set".to_string()));
            };
            match rt.build_function_return_requirements(&a, &target) {
                Ok(requirements) => requirements, Err(message) => return Ok(Err(message)),
            }
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
        CartesianMemberFromCoordinates => match rt.cart_coordinate_membership_requirements(&a, &b) {
            Ok(requirements) => requirements, Err(message) => return Ok(Err(message)),
        },
        IndexCartesianMember => {
            let Obj::SetOperator(SetOperator::IndexCart(cart)) = &b else { return Ok(Err("second argument must be index_cart(...)".to_string())); };
            let carrier = Obj::SetOperator(SetOperator::FamilyUnion(FamilyUnion { left: cart.family_set.clone() }));
            let fn_set = unary_fn(rt, cart.index_set.as_ref().clone(), carrier);
            let choice: AtomicFact = IsChoiceFunctionForFact { fact_id: rt.global_ids.allocate_fact_id(), index: cart.index_set.as_ref().clone(), set: cart.family_set.as_ref().clone(), family: cart.family_fn.as_ref().clone(), choice: a.clone(), line_file: None }.into();
            vec![atomic_in(rt, a, fn_set).into(), choice.into()]
        }
        TupleEqualFromCoordinates => {
            let domain = match rt.tuple_equality_domain(&a, &b)? {
                Ok(domain) => domain, Err(message) => return Ok(Err(message)),
            };
            match rt.tuple_coordinate_equality_requirements(&a, &b, &domain) {
                Ok(requirements) => requirements, Err(message) => return Ok(Err(message)),
            }
        },
        _ => unreachable!(),
    };
    Ok(Ok((requirements, vec![conclusion.into()])))
}
