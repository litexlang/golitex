use crate::ast::fact::{AtomicFact, EqualFact, Fact, InFact, PlainExistFact, QuantifierFreeFact};
use crate::ast::obj::{
    FnObj, FnObjHead, FnSet, FunctionSpace, IdentifierObj, Obj, SetFormer, StructAndFieldAccessObj,
};
use crate::ast::param::{
    ParamType, SetBoundParameterList, TypedParameterGroup, TypedParameterList,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::KnownEqualityPathProof;
use crate::runtime::runtime_ids::IdentifierId;
use crate::runtime::{Runtime, RuntimeResult};
use crate::store_fact_and_infer::{
    InferAtomicExceptEqualityResult, InferInFactEqualFnSetExpandResult,
    InferInFactEqualFnSetTransport, InferInFactFiniteSeqExpandResult, InferInFactFnRangeResult,
    InferInFactSeqExpandResult, StoreFactAndInferResult,
};
use std::collections::HashMap;

impl Runtime {
    // When: `x $in fn(...)` peer / `fn_range(f)` / `finite_seq` / `seq`.
    // Infers: equal-FnSet expand; codomain (+ optional preimage exist); FnSet expand.
    // Example: `z $in fn_range(f)` with `f $in fn(x S) T` ⇒ `z $in T`.
    pub(super) fn infer_in_fact_fn_rules(
        &mut self,
        in_fact: &InFact,
        verify_state: crate::execute::execute_fact_stmt::VerifyState,
    ) -> RuntimeResult<Vec<InferAtomicExceptEqualityResult>> {
        let mut rules = Vec::new();
        if let Some(r) = self.infer_in_fact_equal_fn_set_expand(in_fact, verify_state)? {
            rules.push(r);
        }
        if let Some(r) = self.infer_in_fact_fn_range(in_fact, verify_state)? {
            rules.push(r);
        }
        if let Some(r) = self.infer_in_fact_finite_seq_expand(in_fact, verify_state)? {
            rules.push(r);
        }
        if let Some(r) = self.infer_in_fact_seq_expand(in_fact, verify_state)? {
            rules.push(r);
        }
        Ok(rules)
    }
}

impl Runtime {
    // A checked membership uses the carrier's exact indexed definition.
    // Example: A=finite_seq(R,2), f in A => f in finite_seq(R,2).
    // Literal sequence inference then derives its exact FnSet. A set alias
    // without a member does not construct a callable function.
    fn infer_in_fact_equal_fn_set_expand(
        &mut self,
        in_fact: &InFact,
        verify_state: crate::execute::execute_fact_stmt::VerifyState,
    ) -> RuntimeResult<Option<InferAtomicExceptEqualityResult>> {
        if matches!(
            &in_fact.set,
            Obj::FunctionSpace(FunctionSpace::FnSet(_))
                | Obj::SetFormer(SetFormer::FiniteSeqSet(_) | SetFormer::SeqSet(_))
        ) {
            return Ok(None);
        }
        let mut transports = Vec::new();
        let peers = self.exact_property_object_values(&in_fact.set);
        for (peer, path) in peers {
            if !matches!(
                &peer,
                Obj::FunctionSpace(FunctionSpace::FnSet(_))
                    | Obj::SetFormer(SetFormer::FiniteSeqSet(_) | SetFormer::SeqSet(_))
            ) {
                continue;
            }
            let fact_id = self.global_ids.allocate_fact_id();
            let expanded = AtomicFact::InFact(InFact {
                fact_id,
                element: in_fact.element.clone(),
                set: peer,
                line_file: in_fact.line_file.clone(),
            });
            if let Some(stored) =
                self.try_store_inferred_fact_and_infer(&Fact::AtomicFact(expanded), verify_state)?
            {
                transports.push(InferInFactEqualFnSetTransport {
                    membership_fact_id: in_fact.fact_id,
                    carrier_equal: KnownEqualityPathProof::new(path),
                    derived: stored,
                });
            }
        }
        if transports.is_empty() {
            return Ok(None);
        }
        Ok(Some(
            InferAtomicExceptEqualityResult::InFactEqualFnSetExpand(
                InferInFactEqualFnSetExpandResult { transports },
            ),
        ))
    }

    // When: `z $in fn_range(f)` and f has a visible FnSet body.
    // Infers: `z $in ret_set`; optional preimage exist when z is not already f(args).
    // Example: `have fn f(x R) R = x`, `trust z $in fn_range(f)` ⇒ `z $in R`.
    fn infer_in_fact_fn_range(
        &mut self,
        in_fact: &InFact,
        verify_state: crate::execute::execute_fact_stmt::VerifyState,
    ) -> RuntimeResult<Option<InferAtomicExceptEqualityResult>> {
        let Obj::FunctionSpace(FunctionSpace::FnRange(fn_range)) = &in_fact.set else {
            return Ok(None);
        };
        let Some(body) = self.resolve_fn_set_body_for_fn_range(fn_range.function.as_ref()) else {
            return Ok(None);
        };
        let mut derived: Vec<StoreFactAndInferResult> = Vec::new();
        let codomain_id = self.global_ids.allocate_fact_id();
        let codomain = AtomicFact::InFact(InFact {
            fact_id: codomain_id,
            element: in_fact.element.clone(),
            set: body.ret_set.as_ref().clone(),
            line_file: in_fact.line_file.clone(),
        });
        let Some(stored) =
            self.try_store_inferred_fact_and_infer(&Fact::AtomicFact(codomain), verify_state)?
        else {
            return Ok(None);
        };
        derived.push(stored);

        if !application_is_displayed_preimage(&in_fact.element, fn_range.function.as_ref()) {
            if let Some(exist) =
                self.preimage_exist_fact_from_fn_set(in_fact, fn_range.function.as_ref(), &body)?
            {
                if let Some(stored) =
                    self.try_store_inferred_fact_and_infer(&exist, verify_state)?
                {
                    derived.push(stored);
                }
            }
        }
        Ok(Some(InferAtomicExceptEqualityResult::InFactFnRange(
            InferInFactFnRangeResult { derived },
        )))
    }

    // When: `x $in finite_seq(S, n)`.
    // Infers: `x $in fn(k closed_range(1,n)) S`, with the same exact domain.
    // Example: a typed s in finite_seq(R,3) supplies its one-based FnSet.
    fn infer_in_fact_finite_seq_expand(
        &mut self,
        in_fact: &InFact,
        verify_state: crate::execute::execute_fact_stmt::VerifyState,
    ) -> RuntimeResult<Option<InferAtomicExceptEqualityResult>> {
        let Obj::SetFormer(SetFormer::FiniteSeqSet(_)) = &in_fact.set else {
            return Ok(None);
        };
        let fn_set = self
            .function_space_signature(&in_fact.set)
            .expect("literal finite_seq has an exact function-space signature");
        let fact_id = self.global_ids.allocate_fact_id();
        let expanded = AtomicFact::InFact(InFact {
            fact_id,
            element: in_fact.element.clone(),
            set: Obj::FunctionSpace(FunctionSpace::FnSet(fn_set)),
            line_file: in_fact.line_file.clone(),
        });
        let Some(stored) =
            self.try_store_inferred_fact_and_infer(&Fact::AtomicFact(expanded), verify_state)?
        else {
            return Ok(None);
        };
        Ok(Some(
            InferAtomicExceptEqualityResult::InFactFiniteSeqExpand(
                InferInFactFiniteSeqExpandResult {
                    derived: Box::new(stored),
                },
            ),
        ))
    }

    // When: `x $in seq(S)`.
    // Infers: `x $in fn(i N+) S`.
    // Example: `trust s $in seq(R)` ⇒ `s $in fn(i N+) R`.
    fn infer_in_fact_seq_expand(
        &mut self,
        in_fact: &InFact,
        verify_state: crate::execute::execute_fact_stmt::VerifyState,
    ) -> RuntimeResult<Option<InferAtomicExceptEqualityResult>> {
        let Obj::SetFormer(SetFormer::SeqSet(_)) = &in_fact.set else {
            return Ok(None);
        };
        let fn_set = self
            .function_space_signature(&in_fact.set)
            .expect("literal seq has an exact function-space signature");
        let fact_id = self.global_ids.allocate_fact_id();
        let expanded = AtomicFact::InFact(InFact {
            fact_id,
            element: in_fact.element.clone(),
            set: Obj::FunctionSpace(FunctionSpace::FnSet(fn_set)),
            line_file: in_fact.line_file.clone(),
        });
        let Some(stored) =
            self.try_store_inferred_fact_and_infer(&Fact::AtomicFact(expanded), verify_state)?
        else {
            return Ok(None);
        };
        Ok(Some(InferAtomicExceptEqualityResult::InFactSeqExpand(
            InferInFactSeqExpandResult {
                derived: Box::new(stored),
            },
        )))
    }

    fn resolve_fn_set_body_for_fn_range(&self, function: &Obj) -> Option<FnSet> {
        if let Obj::FunctionSpace(FunctionSpace::AnonymousFn(anon)) = function {
            return Some(anon.body.clone());
        }
        self.collect_in_function_set_candidates(function)
            .into_iter()
            .next()
            .map(|(fn_set, _)| fn_set)
    }

    fn preimage_exist_fact_from_fn_set(
        &mut self,
        in_fact: &InFact,
        function: &Obj,
        body: &FnSet,
    ) -> RuntimeResult<Option<Fact>> {
        let mut binders = Vec::new();
        let mut preimage_objs = Vec::new();
        for group in &body.set_bound_parameters.groups {
            let mut fresh_params = Vec::new();
            for _ in &group.params {
                let binder = self.fresh_internal_param();
                preimage_objs.push(Obj::Identifier(IdentifierObj::from_bound_name(&binder)));
                fresh_params.push(binder);
            }
            if fresh_params.is_empty() {
                continue;
            }
            binders.push(TypedParameterGroup {
                params: fresh_params,
                param_type: ParamType::Obj(group.param_type.as_ref().clone()),
            });
        }
        if binders.is_empty() {
            return Ok(None);
        }
        let subst = set_bound_params_to_arg_map(&body.set_bound_parameters, &preimage_objs);
        let mut facts = Vec::new();
        for dom in &body.dom_facts {
            let Ok(qf) = self.inst_quantifier_free_fact(dom, &subst) else {
                continue;
            };
            facts.push(qf);
        }
        let Some(application) = preimage_application_obj(function, &preimage_objs) else {
            return Ok(None);
        };
        facts.push(QuantifierFreeFact::AtomicFact(AtomicFact::EqualFact(
            EqualFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left: in_fact.element.clone(),
                right: application,
                line_file: in_fact.line_file.clone(),
            },
        )));
        Ok(Some(Fact::ExistFact(PlainExistFact {
            fact_id: self.global_ids.allocate_fact_id(),
            typed_parameters: TypedParameterList { groups: binders },
            facts,
            line_file: in_fact.line_file.clone(),
        })))
    }
}

fn application_is_displayed_preimage(element: &Obj, function: &Obj) -> bool {
    let Obj::FnObj(application) = element else {
        return false;
    };
    let head_obj = match application.head.as_ref() {
        FnObjHead::Object(obj) => obj.as_ref().clone(),
        FnObjHead::Identifier(id) => Obj::Identifier(id.clone()),
        FnObjHead::AnonymousFnLiteral(anon) => {
            Obj::FunctionSpace(FunctionSpace::AnonymousFn(anon.as_ref().clone()))
        }
        FnObjHead::InstantiatedTemplateObj(inst) => Obj::InstantiatedTemplateObj(inst.clone()),
        FnObjHead::FieldAccess(field) => {
            Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::FieldAccess(field.clone()))
        }
    };
    head_obj.ir() == function.ir()
}

fn preimage_application_obj(function: &Obj, args: &[Obj]) -> Option<Obj> {
    let head = match function {
        Obj::Identifier(id) => FnObjHead::Identifier(id.clone()),
        Obj::FunctionSpace(FunctionSpace::AnonymousFn(anon)) => {
            FnObjHead::AnonymousFnLiteral(Box::new(anon.clone()))
        }
        Obj::InstantiatedTemplateObj(inst) => FnObjHead::InstantiatedTemplateObj(inst.clone()),
        Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::FieldAccess(field)) => {
            FnObjHead::FieldAccess(field.clone())
        }
        _ => return None,
    };
    let group = args.iter().cloned().map(Box::new).collect();
    Some(Obj::FnObj(FnObj {
        head: Box::new(head),
        body: vec![group],
    }))
}

fn set_bound_params_to_arg_map(
    list: &SetBoundParameterList,
    args: &[Obj],
) -> HashMap<IdentifierId, Obj> {
    let mut map = HashMap::new();
    let mut i = 0;
    for group in &list.groups {
        for param in &group.params {
            if i >= args.len() {
                break;
            }
            map.insert(param.id, args[i].clone());
            i += 1;
        }
    }
    map
}
