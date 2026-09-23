use crate::new_pipeline::ast::fact::{
    AtomicFact, ExistOrAndChainAtomicFact, Fact, ForallFact, InFact, NormalAtomicFact,
    PlainExistFact, QuantifierFreeFact,
};
use crate::new_pipeline::ast::names::AtomicName;
use crate::new_pipeline::ast::obj::{
    FamilyUnion, FnObj, FnObjHead, FnSet, FunctionSpace, IdentifierObj, Obj, SetOperator,
};
use crate::new_pipeline::ast::param::{
    ParamType, SetBoundParameterGroup, SetBoundParameterList, TypedParameterGroup, TypedParameterList,
};
use crate::new_pipeline::parse::keywords::IS_CHOICE_FUNCTION_FOR;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};
use crate::new_pipeline::store_fact_and_infer::{
    InferAtomicExceptEqualityResult, InferInFactFamilyUnionResult, InferInFactIndexCartResult,
    InferInFactIndexIntersectResult, InferInFactIndexUnionResult, StoreFactAndInferResult,
};

impl Runtime {
    // When: `x $in family_union(F)` / `index_union` / `index_intersect` / `index_cart`.
    // Infers: exist member / ambient + exist fiber / ambient + forall fiber /
    // FnSet + `$is_choice_function_for`.
    // Example: `x $in family_union(F)` ⇒ `exist item F st {x $in item}`.
    pub(super) fn infer_in_fact_index_family_rules(
        &mut self,
        in_fact: &InFact,
    ) -> RuntimeResult<Vec<InferAtomicExceptEqualityResult>> {
        let mut rules = Vec::new();
        if let Some(r) = self.infer_in_fact_family_union(in_fact)? {
            rules.push(r);
        }
        if let Some(r) = self.infer_in_fact_index_union(in_fact)? {
            rules.push(r);
        }
        if let Some(r) = self.infer_in_fact_index_intersect(in_fact)? {
            rules.push(r);
        }
        if let Some(r) = self.infer_in_fact_index_cart(in_fact)? {
            rules.push(r);
        }
        Ok(rules)
    }
}

impl Runtime {
    fn infer_in_fact_family_union(
        &mut self,
        in_fact: &InFact,
    ) -> RuntimeResult<Option<InferAtomicExceptEqualityResult>> {
        let Obj::SetOperator(SetOperator::FamilyUnion(family_union)) = &in_fact.set else {
            return Ok(None);
        };
        let binder = self.fresh_internal_param();
        let member_obj = Obj::Identifier(IdentifierObj::from_bound_name(&binder));
        let body_in = AtomicFact::InFact(InFact {
            fact_id: self.global_ids.allocate_fact_id(),
            element: in_fact.element.clone(),
            set: member_obj,
            line_file: in_fact.line_file.clone(),
        });
        let exist = Fact::ExistFact(PlainExistFact {
            fact_id: self.global_ids.allocate_fact_id(),
            typed_parameters: TypedParameterList {
                groups: vec![TypedParameterGroup {
                    params: vec![binder],
                    param_type: ParamType::Obj(family_union.left.as_ref().clone()),
                }],
            },
            facts: vec![QuantifierFreeFact::AtomicFact(body_in)],
            line_file: in_fact.line_file.clone(),
        });
        let Some(stored) = self.try_store_inferred_fact_and_infer(&exist)? else {
            return Ok(None);
        };
        Ok(Some(
            InferAtomicExceptEqualityResult::InFactFamilyUnion(InferInFactFamilyUnionResult {
                derived: Box::new(stored),
            }),
        ))
    }

    fn infer_in_fact_index_union(
        &mut self,
        in_fact: &InFact,
    ) -> RuntimeResult<Option<InferAtomicExceptEqualityResult>> {
        let Obj::SetOperator(SetOperator::IndexUnion(index_union)) = &in_fact.set else {
            return Ok(None);
        };
        let mut derived: Vec<StoreFactAndInferResult> = Vec::new();
        let ambient_id = self.global_ids.allocate_fact_id();
        let ambient = AtomicFact::InFact(InFact {
            fact_id: ambient_id,
            element: in_fact.element.clone(),
            set: index_union.ambient_set.as_ref().clone(),
            line_file: in_fact.line_file.clone(),
        });
        if let Some(stored) = self.try_store_inferred_fact_and_infer(&Fact::AtomicFact(ambient))? {
            derived.push(stored);
        }

        let binder = self.fresh_internal_param();
        let index_obj = Obj::Identifier(IdentifierObj::from_bound_name(&binder));
        let Some(fiber) =
            indexed_family_application(index_union.family_fn.as_ref(), index_obj.clone())
        else {
            if derived.is_empty() {
                return Ok(None);
            }
            return Ok(Some(
                InferAtomicExceptEqualityResult::InFactIndexUnion(InferInFactIndexUnionResult {
                    derived,
                }),
            ));
        };
        let element_in_fiber = AtomicFact::InFact(InFact {
            fact_id: self.global_ids.allocate_fact_id(),
            element: in_fact.element.clone(),
            set: fiber,
            line_file: in_fact.line_file.clone(),
        });
        let exist = Fact::ExistFact(PlainExistFact {
            fact_id: self.global_ids.allocate_fact_id(),
            typed_parameters: TypedParameterList {
                groups: vec![TypedParameterGroup {
                    params: vec![binder],
                    param_type: ParamType::Obj(index_union.index_set.as_ref().clone()),
                }],
            },
            facts: vec![QuantifierFreeFact::AtomicFact(element_in_fiber)],
            line_file: in_fact.line_file.clone(),
        });
        if let Some(stored) = self.try_store_inferred_fact_and_infer(&exist)? {
            derived.push(stored);
        }
        if derived.is_empty() {
            return Ok(None);
        }
        Ok(Some(
            InferAtomicExceptEqualityResult::InFactIndexUnion(InferInFactIndexUnionResult {
                derived,
            }),
        ))
    }

    fn infer_in_fact_index_intersect(
        &mut self,
        in_fact: &InFact,
    ) -> RuntimeResult<Option<InferAtomicExceptEqualityResult>> {
        let Obj::SetOperator(SetOperator::IndexIntersect(index_intersect)) = &in_fact.set else {
            return Ok(None);
        };
        let mut derived: Vec<StoreFactAndInferResult> = Vec::new();
        let ambient_id = self.global_ids.allocate_fact_id();
        let ambient = AtomicFact::InFact(InFact {
            fact_id: ambient_id,
            element: in_fact.element.clone(),
            set: index_intersect.ambient_set.as_ref().clone(),
            line_file: in_fact.line_file.clone(),
        });
        if let Some(stored) = self.try_store_inferred_fact_and_infer(&Fact::AtomicFact(ambient))? {
            derived.push(stored);
        }

        let binder = self.fresh_internal_param();
        let index_obj = Obj::Identifier(IdentifierObj::from_bound_name(&binder));
        let Some(fiber) =
            indexed_family_application(index_intersect.family_fn.as_ref(), index_obj.clone())
        else {
            if derived.is_empty() {
                return Ok(None);
            }
            return Ok(Some(
                InferAtomicExceptEqualityResult::InFactIndexIntersect(
                    InferInFactIndexIntersectResult { derived },
                ),
            ));
        };
        let element_in_fiber = AtomicFact::InFact(InFact {
            fact_id: self.global_ids.allocate_fact_id(),
            element: in_fact.element.clone(),
            set: fiber,
            line_file: in_fact.line_file.clone(),
        });
        let forall = Fact::ForallFact(ForallFact {
            fact_id: self.global_ids.allocate_fact_id(),
            typed_parameters: TypedParameterList {
                groups: vec![TypedParameterGroup {
                    params: vec![binder],
                    param_type: ParamType::Obj(index_intersect.index_set.as_ref().clone()),
                }],
            },
            dom_facts: Vec::new(),
            then_facts: vec![ExistOrAndChainAtomicFact::AtomicFact(element_in_fiber)],
            line_file: in_fact.line_file.clone(),
        });
        if let Some(stored) = self.try_store_inferred_fact_and_infer(&forall)? {
            derived.push(stored);
        }
        if derived.is_empty() {
            return Ok(None);
        }
        Ok(Some(
            InferAtomicExceptEqualityResult::InFactIndexIntersect(
                InferInFactIndexIntersectResult { derived },
            ),
        ))
    }

    // When: `f $in index_cart(I, S, g)`.
    // Infers: `f $in fn(alpha I) family_union(S)` and `$is_choice_function_for(I, S, g, f)`.
    // Example: trust `f $in index_cart({1}, R, g)` ⇒ `$is_choice_function_for({1}, R, g, f)`.
    fn infer_in_fact_index_cart(
        &mut self,
        in_fact: &InFact,
    ) -> RuntimeResult<Option<InferAtomicExceptEqualityResult>> {
        let Obj::SetOperator(SetOperator::IndexCart(index_cart)) = &in_fact.set else {
            return Ok(None);
        };
        let mut derived: Vec<StoreFactAndInferResult> = Vec::new();

        let binder = self.fresh_internal_param();
        let fn_set = Obj::FunctionSpace(FunctionSpace::FnSet(FnSet {
            set_bound_parameters: SetBoundParameterList {
                groups: vec![SetBoundParameterGroup {
                    params: vec![binder],
                    param_type: Box::new(index_cart.index_set.as_ref().clone()),
                }],
            },
            dom_facts: Vec::new(),
            ret_set: Box::new(Obj::SetOperator(SetOperator::FamilyUnion(FamilyUnion {
                left: Box::new(index_cart.family_set.as_ref().clone()),
            }))),
        }));
        let fn_set_in = AtomicFact::InFact(InFact {
            fact_id: self.global_ids.allocate_fact_id(),
            element: in_fact.element.clone(),
            set: fn_set,
            line_file: in_fact.line_file.clone(),
        });
        if let Some(stored) = self.try_store_inferred_fact_and_infer(&Fact::AtomicFact(fn_set_in))?
        {
            derived.push(stored);
        }

        let choice = AtomicFact::NormalAtomicFact(NormalAtomicFact {
            fact_id: self.global_ids.allocate_fact_id(),
            predicate: AtomicName::plain(IS_CHOICE_FUNCTION_FOR.to_string()),
            body: vec![
                index_cart.index_set.as_ref().clone(),
                index_cart.family_set.as_ref().clone(),
                index_cart.family_fn.as_ref().clone(),
                in_fact.element.clone(),
            ],
            line_file: in_fact.line_file.clone(),
        });
        if let Some(stored) = self.try_store_inferred_fact_and_infer(&Fact::AtomicFact(choice))? {
            derived.push(stored);
        }

        if derived.is_empty() {
            return Ok(None);
        }
        Ok(Some(InferAtomicExceptEqualityResult::InFactIndexCart(
            InferInFactIndexCartResult { derived },
        )))
    }
}

fn indexed_family_application(family_fn: &Obj, index: Obj) -> Option<Obj> {
    let head = match family_fn {
        Obj::Identifier(id) => FnObjHead::Identifier(id.clone()),
        Obj::FunctionSpace(FunctionSpace::AnonymousFn(anon)) => {
            FnObjHead::AnonymousFnLiteral(Box::new(anon.clone()))
        }
        Obj::InstantiatedTemplateObj(inst) => FnObjHead::InstantiatedTemplateObj(inst.clone()),
        _ => return None,
    };
    Some(Obj::FnObj(FnObj {
        head: Box::new(head),
        body: vec![vec![Box::new(index)]],
    }))
}
