use crate::ast::fact::{
    AtomicFact, EqualFact, Fact, InFact, LessEqualFact, PlainExistFact, QuantifierFreeFact,
};
use crate::ast::obj::{
    FnObj, FnObjHead, FnSet, FunctionSpace, IdentifierObj, Obj, SetFormer, StandardSet,
};
use crate::ast::param::{
    ParamType, SetBoundParameterGroup, SetBoundParameterList, TypedParameterGroup, TypedParameterList,
};
use crate::runtime::runtime_ids::IdentifierId;
use crate::runtime::{Runtime, RuntimeResult};
use crate::store_fact_and_infer::{
    InferAtomicExceptEqualityResult, InferInFactEqualFnSetExpandResult,
    InferInFactFiniteSeqExpandResult, InferInFactFnRangeResult, InferInFactSeqExpandResult,
    StoreFactAndInferResult,
};
use std::collections::HashMap;

impl Runtime {
    // When: `x $in fn(...)` peer / `fn_range(f)` / `finite_seq` / `seq`.
    // Infers: equal-FnSet expand; codomain (+ optional preimage exist); FnSet expand.
    // Example: `z $in fn_range(f)` with `f $in fn(x S) T` ⇒ `z $in T`.
    pub(super) fn infer_in_fact_fn_rules(
        &mut self,
        in_fact: &InFact,
     verify_state: crate::execute::execute_fact_stmt::VerifyState) -> RuntimeResult<Vec<InferAtomicExceptEqualityResult>> {
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
    // When: `x $in S` and some equality peer of S is a literal FnSet.
    // Infers: `x $in FnSet` (store registers InFunctionSet).
    // Example: `A = fn(x R) R`, `trust f $in A` ⇒ `f $in fn(x R) R`.
    fn infer_in_fact_equal_fn_set_expand(
        &mut self,
        in_fact: &InFact,
     verify_state: crate::execute::execute_fact_stmt::VerifyState) -> RuntimeResult<Option<InferAtomicExceptEqualityResult>> {
        if matches!(
            &in_fact.set,
            Obj::FunctionSpace(FunctionSpace::FnSet(_))
        ) {
            return Ok(None);
        }
        let mut derived: Vec<StoreFactAndInferResult> = Vec::new();
        let adjacency = self.visible_equivalence_class_adjacency();
        let Some(neighbors) = adjacency.get(&in_fact.set.ir()) else {
            return Ok(None);
        };
        for (_peer_key, equal_fact) in neighbors.iter() {
            let peer = if equal_fact.left.ir() == in_fact.set.ir() {
                &equal_fact.right
            } else {
                &equal_fact.left
            };
            let Obj::FunctionSpace(FunctionSpace::FnSet(fn_set)) = peer else {
                continue;
            };
            let fact_id = self.global_ids.allocate_fact_id();
            let expanded = AtomicFact::InFact(InFact {
                fact_id,
                element: in_fact.element.clone(),
                set: Obj::FunctionSpace(FunctionSpace::FnSet(fn_set.clone())),
                line_file: in_fact.line_file.clone(),
            });
            if let Some(stored) =
                self.try_store_inferred_fact_and_infer(&Fact::AtomicFact(expanded), verify_state)?
            {
                derived.push(stored);
            }
        }
        if derived.is_empty() {
            return Ok(None);
        }
        Ok(Some(
            InferAtomicExceptEqualityResult::InFactEqualFnSetExpand(
                InferInFactEqualFnSetExpandResult { derived },
            ),
        ))
    }

    // When: `z $in fn_range(f)` and f has a visible FnSet body.
    // Infers: `z $in ret_set`; optional preimage exist when z is not already f(args).
    // Example: `have fn f(x R) R = x`, `trust z $in fn_range(f)` ⇒ `z $in R`.
    fn infer_in_fact_fn_range(
        &mut self,
        in_fact: &InFact,
     verify_state: crate::execute::execute_fact_stmt::VerifyState) -> RuntimeResult<Option<InferAtomicExceptEqualityResult>> {
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
        let Some(stored) = self.try_store_inferred_fact_and_infer(&Fact::AtomicFact(codomain), verify_state)?
        else {
            return Ok(None);
        };
        derived.push(stored);

        if !application_is_displayed_preimage(&in_fact.element, fn_range.function.as_ref()) {
            if let Some(exist) =
                self.preimage_exist_fact_from_fn_set(in_fact, fn_range.function.as_ref(), &body)?
            {
                if let Some(stored) = self.try_store_inferred_fact_and_infer(&exist, verify_state)? {
                    derived.push(stored);
                }
            }
        }
        Ok(Some(InferAtomicExceptEqualityResult::InFactFnRange(
            InferInFactFnRangeResult { derived },
        )))
    }

    // When: `x $in finite_seq(S, n)`.
    // Infers: `x $in fn(i N+: i <= n) S` (registers InFunctionSet on store).
    // Example: `trust s $in finite_seq(R, 3)` ⇒ `s $in fn(i N+: i <= 3) R`.
    fn infer_in_fact_finite_seq_expand(
        &mut self,
        in_fact: &InFact,
     verify_state: crate::execute::execute_fact_stmt::VerifyState) -> RuntimeResult<Option<InferAtomicExceptEqualityResult>> {
        let Obj::SetFormer(SetFormer::FiniteSeqSet(fs)) = &in_fact.set else {
            return Ok(None);
        };
        let fn_set = self.finite_seq_set_to_fn_set(fs, in_fact.line_file.clone());
        let fact_id = self.global_ids.allocate_fact_id();
        let expanded = AtomicFact::InFact(InFact {
            fact_id,
            element: in_fact.element.clone(),
            set: Obj::FunctionSpace(FunctionSpace::FnSet(fn_set)),
            line_file: in_fact.line_file.clone(),
        });
        let Some(stored) = self.try_store_inferred_fact_and_infer(&Fact::AtomicFact(expanded), verify_state)?
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
     verify_state: crate::execute::execute_fact_stmt::VerifyState) -> RuntimeResult<Option<InferAtomicExceptEqualityResult>> {
        let Obj::SetFormer(SetFormer::SeqSet(ss)) = &in_fact.set else {
            return Ok(None);
        };
        let fn_set = self.seq_set_to_fn_set(ss);
        let fact_id = self.global_ids.allocate_fact_id();
        let expanded = AtomicFact::InFact(InFact {
            fact_id,
            element: in_fact.element.clone(),
            set: Obj::FunctionSpace(FunctionSpace::FnSet(fn_set)),
            line_file: in_fact.line_file.clone(),
        });
        let Some(stored) = self.try_store_inferred_fact_and_infer(&Fact::AtomicFact(expanded), verify_state)?
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

    fn finite_seq_set_to_fn_set(
        &mut self,
        fs: &crate::ast::obj::FiniteSeqSet,
        line_file: Option<crate::ast::line_file::SourceLine>,
    ) -> FnSet {
        let binder = self.fresh_internal_param();
        let binder_obj = Obj::Identifier(IdentifierObj::from_bound_name(&binder));
        FnSet {
            set_bound_parameters: SetBoundParameterList {
                groups: vec![SetBoundParameterGroup {
                    params: vec![binder],
                    param_type: Box::new(Obj::StandardSet(StandardSet::NPos)),
                }],
            },
            dom_facts: vec![QuantifierFreeFact::AtomicFact(AtomicFact::LessEqualFact(
                LessEqualFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    left: binder_obj,
                    right: fs.n.as_ref().clone(),
                    line_file: line_file.clone(),
                },
            ))],
            ret_set: Box::new(fs.set.as_ref().clone()),
        }
    }

    fn seq_set_to_fn_set(&mut self, ss: &crate::ast::obj::SeqSet) -> FnSet {
        let binder = self.fresh_internal_param();
        FnSet {
            set_bound_parameters: SetBoundParameterList {
                groups: vec![SetBoundParameterGroup {
                    params: vec![binder],
                    param_type: Box::new(Obj::StandardSet(StandardSet::NPos)),
                }],
            },
            dom_facts: Vec::new(),
            ret_set: Box::new(ss.set.as_ref().clone()),
        }
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
        FnObjHead::Identifier(id) => Obj::Identifier(id.clone()),
        FnObjHead::AnonymousFnLiteral(anon) => {
            Obj::FunctionSpace(FunctionSpace::AnonymousFn(anon.as_ref().clone()))
        }
        FnObjHead::InstantiatedTemplateObj(inst) => Obj::InstantiatedTemplateObj(inst.clone()),
        FnObjHead::FieldAccess(_) => return false,
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
