use super::obj_well_defined_by_def_common::ObjWellDefinedByDefCommonStages;
use crate::ast::obj::{
    FieldAccess, FnObjHead, FnSet, FunctionSpace, Obj, StructAndFieldAccessObj,
};
use crate::ast::param::{
    ParamType, SetBoundParameterList, TypedParameterGroup, TypedParameterList,
};
use crate::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::execute::execute_fact_stmt::VerifyState;
use crate::instantiate::collect_free_plain_ids;
use crate::runtime::runtime_ids::IdentifierId;
use crate::runtime::{Runtime, RuntimeResult};
use std::collections::{HashMap, HashSet};

impl Runtime {
    pub(super) fn verify_objs_as_children(
        &mut self,
        objs: &[&Obj],
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        let mut child_obj_well_defined = Vec::new();
        for obj in objs {
            child_obj_well_defined
                .push(self.verify_obj_well_definedness(obj, verify_state.clone())?);
        }
        Ok(ObjWellDefinedByDefCommonStages::from_children(
            child_obj_well_defined,
        ))
    }

    pub(super) fn verify_boxed_objs_as_children(
        &mut self,
        objs: &[Box<Obj>],
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        let refs: Vec<&Obj> = objs.iter().map(|o| o.as_ref()).collect();
        self.verify_objs_as_children(&refs, verify_state)
    }

    pub(super) fn verify_unary_obj_well_definedness_by_def(
        &mut self,
        arg: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        self.verify_objs_as_children(&[arg], verify_state)
    }

    pub(super) fn verify_binary_obj_well_definedness_by_def(
        &mut self,
        left: &Obj,
        right: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        self.verify_objs_as_children(&[left, right], verify_state)
    }

    pub(super) fn with_requirements(
        &self,
        proof: ObjWellDefinedByDefCommonStages,
        requirement_fact_verified: Vec<VerifyFactResult>,
    ) -> ObjWellDefinedByDefCommonStages {
        proof.with_requirements(requirement_fact_verified)
    }

    // Resolve a callable's FnSet: anonymous literal, bare name with InFunctionSet, or
    // identifier-headed empty application. Used by iterated / reduce WD.
    pub(in crate::execute) fn resolve_callable_fn_set(&self, function: &Obj) -> Option<FnSet> {
        match function {
            Obj::FunctionSpace(FunctionSpace::AnonymousFn(anon)) => Some(anon.body.clone()),
            Obj::FnObj(fo) if fo.body.is_empty() => match fo.head.as_ref() {
                FnObjHead::AnonymousFnLiteral(a) => Some(a.body.clone()),
                FnObjHead::Identifier(id) => {
                    let head = Obj::Identifier(id.clone());
                    self.collect_in_function_set_candidates(&head)
                        .into_iter()
                        .next()
                        .map(|(fs, _)| fs)
                }
                FnObjHead::InstantiatedTemplateObj(inst) => {
                    let head = Obj::InstantiatedTemplateObj(inst.clone());
                    self.collect_in_function_set_candidates(&head)
                        .into_iter()
                        .next()
                        .map(|(fs, _)| fs)
                }
                FnObjHead::FieldAccess(access) => {
                    let head = Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::FieldAccess(
                        access.clone(),
                    ));
                    if let Some(fs) = self
                        .collect_in_function_set_candidates(&head)
                        .into_iter()
                        .next()
                        .map(|(fs, _)| fs)
                    {
                        return Some(fs);
                    }
                    match self.resolve_field_access_field_type(access)? {
                        Obj::FunctionSpace(FunctionSpace::FnSet(fs)) => Some(fs),
                        Obj::FunctionSpace(FunctionSpace::AnonymousFn(anon)) => Some(anon.body),
                        _ => None,
                    }
                }
            },
            _ => self
                .collect_in_function_set_candidates(function)
                .into_iter()
                .next()
                .map(|(fs, _)| fs),
        }
    }

    // Last field's declared type along a FieldAccess path (definition-time carrier walk).
    pub(super) fn resolve_field_access_field_type(&self, access: &FieldAccess) -> Option<Obj> {
        if access.fields.is_empty() {
            return None;
        }
        let mut carrier = self.resolve_definition_struct_carrier(access.obj.as_ref())?;
        for (index, field_name) in access.fields.iter().enumerate() {
            let def = self.def_struct_visible(&carrier.name)?;
            let field = def.fields.iter().find(|f| f.binding.name == *field_name)?;
            let is_last = index + 1 == access.fields.len();
            if is_last {
                return Some(field.field_type.clone());
            }
            match &field.field_type {
                Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::StructObj(next)) => {
                    carrier = next.clone();
                }
                _ => return None,
            }
        }
        None
    }
}

// Head object for a FnObj (used when looking up InFunctionSet / field type).
pub(super) fn fn_obj_head_as_obj(head: &FnObjHead) -> Obj {
    match head {
        FnObjHead::Identifier(id) => Obj::Identifier(id.clone()),
        FnObjHead::InstantiatedTemplateObj(inst) => Obj::InstantiatedTemplateObj(inst.clone()),
        FnObjHead::FieldAccess(access) => {
            Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::FieldAccess(access.clone()))
        }
        FnObjHead::AnonymousFnLiteral(a) => {
            Obj::FunctionSpace(FunctionSpace::AnonymousFn(a.as_ref().clone()))
        }
    }
}

pub(super) fn set_bound_parameters_to_typed_parameter_list(
    list: &SetBoundParameterList,
) -> TypedParameterList {
    TypedParameterList {
        groups: list
            .groups
            .iter()
            .map(|group| TypedParameterGroup {
                params: group.params.clone(),
                param_type: ParamType::Obj(group.param_type.as_ref().clone()),
            })
            .collect(),
    }
}

pub(super) fn set_bound_parameter_count(list: &SetBoundParameterList) -> usize {
    let mut n = 0;
    for group in &list.groups {
        n += group.params.len();
    }
    n
}

pub(super) fn set_bound_params_to_arg_map(
    list: &SetBoundParameterList,
    args: &[Obj],
) -> HashMap<IdentifierId, Obj> {
    let mut map = HashMap::new();
    let mut i = 0;
    for group in &list.groups {
        for param in &group.params {
            if i < args.len() {
                map.insert(param.id, args[i].clone());
            }
            i += 1;
        }
    }
    map
}

// FnSet / AnonymousFn obj carriers must be fixed sets: a later group's
// `param_type` must not freely mention an earlier binder of the same signature.
// Example reject: `fn(x R, y S(x))`.
//
// Why forall may look similar but is allowed: `forall S set, x S` uses binder
// *kinds* on TypedParameterList (`ParamType::Set`, then `Obj(S)`). That is a
// telescope over "introduce a set, then an element of it", not a function
// domain object. A set-theoretic function signature must fix each ordinary
// domain set up front, so SetBoundParameterList forbids the same dependence.
// Kind telescopes stay on introduce_typed_parameters (sequential). Return sets
// and `: dom_facts` may still cite parameters after binders are introduced.
//
// Returns the failing group index when a citation is found.
pub(super) fn set_bound_param_type_cites_earlier_binder(
    list: &SetBoundParameterList,
) -> Option<usize> {
    let mut earlier_binders = HashSet::new();
    let empty_bound = HashSet::new();
    for (index, group) in list.groups.iter().enumerate() {
        let mut free = HashSet::new();
        collect_free_plain_ids(group.param_type.as_ref(), &empty_bound, &mut free);
        for id in &free {
            if earlier_binders.contains(id) {
                return Some(index);
            }
        }
        for param in &group.params {
            earlier_binders.insert(param.id);
        }
    }
    None
}
