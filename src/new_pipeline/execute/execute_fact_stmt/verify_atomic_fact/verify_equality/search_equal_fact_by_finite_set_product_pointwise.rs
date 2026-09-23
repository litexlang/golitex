use super::by_builtin_strategy_result::FiniteSetProductPointwiseEqualityStrategySingleStep;
use crate::new_pipeline::ast::fact::{EqualFact, Fact};
use crate::new_pipeline::ast::obj::{AnonymousFn, FnObj, FnObjHead, IdentifierObj, Obj, FunctionSpace, IteratedOperator, StructAndFieldAccessObj};
use crate::new_pipeline::ast::param::{ParamType, SetBoundParameterList, TypedParameterGroup, TypedParameterList};
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::runtime_ids::IdentifierId;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};
use std::collections::HashMap;

impl Runtime {
    // Builtin strategy: finite_set_product congruence by pointwise factors.
    // Mathematical property / examples: see FiniteSetProductPointwiseEqualityStrategySingleStep.
    pub fn search_equal_fact_by_finite_set_product_pointwise(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<FiniteSetProductPointwiseEqualityStrategySingleStep>> {
        let (Obj::IteratedOperator(IteratedOperator::ProductOfFiniteSet(left)), Obj::IteratedOperator(IteratedOperator::ProductOfFiniteSet(right))) =
            (&fact.left, &fact.right)
        else {
            return Ok(None);
        };

        let binder = self.fresh_internal_param();
        let x_obj = Obj::Identifier(IdentifierObj::from_bound_name(&binder));
        let Some(left_at_x) = unary_function_at(self, left.func.as_ref(), &x_obj) else {
            return Ok(None);
        };
        let Some(right_at_x) = unary_function_at(self, right.func.as_ref(), &x_obj) else {
            return Ok(None);
        };

        let child_state = verify_state.without_well_defined_storage();
        let mut requirement_facts = Vec::with_capacity(2);
        let mut proof_of_requirement_facts = Vec::with_capacity(2);

        let set_goal: Fact = EqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: left.set.as_ref().clone(),
            right: right.set.as_ref().clone(),
            line_file: fact.line_file.clone(),
        }
        .into();
        let set_proof = self.verify_fact(&set_goal, child_state.clone())?;
        if set_proof.is_failed() {
            return Ok(None);
        }
        requirement_facts.push(set_goal);
        proof_of_requirement_facts.push(set_proof);

        let pointwise_goal: Fact = EqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: left_at_x,
            right: right_at_x,
            line_file: fact.line_file.clone(),
        }
        .into();
        let pointwise_set = left.set.as_ref().clone();
        let (pointwise_proof, _local_env) = self.run_in_local_env_and_take_env(|rt| {
            let params = TypedParameterList {
                groups: vec![TypedParameterGroup {
                    params: vec![binder.clone()],
                    param_type: ParamType::Obj(pointwise_set.clone()),
                }],
            };
            rt.define_typed_parameters_in_current_env(&params, None)?;
            rt.verify_fact(&pointwise_goal, child_state.clone())
        })?;
        if pointwise_proof.is_failed() {
            return Ok(None);
        }
        requirement_facts.push(pointwise_goal);
        proof_of_requirement_facts.push(pointwise_proof);

        Ok(Some(FiniteSetProductPointwiseEqualityStrategySingleStep {
            requirement_facts,
            proof_of_requirement_facts,
        }))
    }
}

// Apply a unary function object at `x`: anonymous body substitution, or `f(x)`.
fn unary_function_at(rt: &mut Runtime, func: &Obj, x: &Obj) -> Option<Obj> {
    if let Some(af) = as_unary_anonymous_fn(func) {
        let param_id = first_set_bound_param_id(&af.body.set_bound_parameters)?;
        let mut subst: HashMap<IdentifierId, Obj> = HashMap::new();
        subst.insert(param_id, x.clone());
        return rt.inst_obj(af.equal_to.as_ref(), &subst).ok();
    }
    if let Obj::FnObj(fo) = func {
        if !fo.body.is_empty() {
            return None;
        }
        return Some(Obj::FnObj(FnObj {
            head: fo.head.clone(),
            body: vec![vec![Box::new(x.clone())]],
        }));
    }
    let head = match func {
        Obj::Identifier(id) => FnObjHead::Identifier(id.clone()),
        Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::FieldAccess(v)) => {
            FnObjHead::FieldAccess(v.clone())
        }
        Obj::InstantiatedTemplateObj(v) => FnObjHead::InstantiatedTemplateObj(v.clone()),
        Obj::FunctionSpace(FunctionSpace::AnonymousFn(af)) => FnObjHead::AnonymousFnLiteral(Box::new(af.clone())),
        _ => return None,
    };
    Some(Obj::FnObj(FnObj {
        head: Box::new(head),
        body: vec![vec![Box::new(x.clone())]],
    }))
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

fn first_set_bound_param_id(list: &SetBoundParameterList) -> Option<IdentifierId> {
    let mut count = 0;
    let mut first = None;
    for group in &list.groups {
        for param in &group.params {
            if first.is_none() {
                first = Some(param.id);
            }
            count += 1;
        }
    }
    if count == 1 {
        first
    } else {
        None
    }
}
