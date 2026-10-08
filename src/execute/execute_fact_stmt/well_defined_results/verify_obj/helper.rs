use super::obj_well_defined_by_def_common::ObjWellDefinedByDefCommonStages;
use crate::ast::obj::{
    FieldAccess, FnObjHead, FnSet, FunctionSpace, Obj, StructAndFieldAccessObj, StructObj,
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

pub(super) struct CheckedFunctionPrefixSignatureProof {
    pub signature: FnSet,
    pub source: VerifyFactResult,
}

impl Runtime {
    // A common return upper bound may hide a function-valued coordinate.
    // Consume an actual checked member of the strictly shorter call prefix;
    // the caller has already checked all earlier arguments and guards.
    pub(super) fn verify_stored_prefix_function_signature(
        &mut self,
        prefix: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<CheckedFunctionPrefixSignatureProof>> {
        // A fixed Cartesian position has its own carrier, even when the
        // enclosing function's common return upper bound is a union.
        // Read only declared carriers here; verify the actual shorter
        // application membership below before consuming its signature.
        if let Some(shape) = self.lookup_known_tuple_shape(prefix) {
            if let Some(cart) = shape.cart() {
                let set = Obj::ProductShape(crate::ast::obj::ProductShape::Cart(cart.clone()));
                let signature = self.cart_function_signature(cart);
                let membership = crate::ast::fact::Fact::AtomicFact(
                    crate::ast::fact::AtomicFact::InFact(crate::ast::fact::InFact {
                        fact_id: self.global_ids.allocate_fact_id(),
                        element: prefix.clone(),
                        set,
                        line_file: None,
                    }),
                );
                let proof = self.verify_fact(&membership, verify_state)?;
                if !proof.is_failed() {
                    return Ok(Some(CheckedFunctionPrefixSignatureProof {
                        signature,
                        source: proof,
                    }));
                }
            }
        }
        for (signature, _) in self.collect_in_function_set_candidates(prefix) {
            let membership = crate::ast::fact::Fact::AtomicFact(
                crate::ast::fact::AtomicFact::InFact(crate::ast::fact::InFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    element: prefix.clone(),
                    set: Obj::FunctionSpace(FunctionSpace::FnSet(signature.clone())),
                    line_file: None,
                }),
            );
            let proof = self.verify_fact(&membership, verify_state)?;
            if !proof.is_failed() {
                return Ok(Some(CheckedFunctionPrefixSignatureProof {
                    signature,
                    source: proof,
                }));
            }
        }
        // A literal tuple's common return bound contains singleton values,
        // so it need not itself expose a Cartesian carrier. Use the checked
        // beta value of this strictly shorter application, and retain a real
        // equality proof before consuming that value's complete domain.
        let super::entry::VerifyObjWellDefinedResult::Success(prefix_wd) =
            self.verify_obj_well_definedness(prefix, verify_state)?
        else {
            return Ok(None);
        };
        if let Some((_, value)) = self.parent_checked_beta_body(prefix, &prefix_wd, verify_state)? {
            let (signatures, intrinsic) = match &value {
                Obj::FunctionSpace(FunctionSpace::AnonymousFn(function)) => {
                    (vec![function.body.clone()], true)
                }
                Obj::ProductShape(crate::ast::obj::ProductShape::Tuple(_)) => (
                    self.finite_function_signatures(&value)
                        .into_iter()
                        .map(|proof| proof.signature)
                        .collect(),
                    true,
                ),
                _ => (
                    self.collect_in_function_set_candidates(&value)
                        .into_iter()
                        .map(|(signature, _)| signature)
                        .collect(),
                    false,
                ),
            };
            for signature in signatures {
                let equality = crate::ast::fact::EqualFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    left: prefix.clone(),
                    right: value.clone(),
                    line_file: None,
                };
                let goal = if intrinsic {
                    crate::ast::fact::Fact::from(equality)
                } else {
                    // An identifier/field/template needs its real complete
                    // membership as well as the coordinate equality. Retain
                    // both certificates, rather than just copying a signature.
                    let member = crate::ast::fact::InFact {
                        fact_id: self.global_ids.allocate_fact_id(),
                        element: value.clone(),
                        set: Obj::FunctionSpace(FunctionSpace::FnSet(signature.clone())),
                        line_file: None,
                    };
                    crate::ast::fact::Fact::AndFact(crate::ast::fact::AndFact {
                        fact_id: self.global_ids.allocate_fact_id(),
                        facts: vec![equality.into(), member.into()],
                        line_file: None,
                    })
                };
                let proof = self.verify_fact(&goal, verify_state)?;
                if !proof.is_failed() {
                    return Ok(Some(CheckedFunctionPrefixSignatureProof {
                        signature,
                        source: proof,
                    }));
                }
            }
        }
        Ok(None)
    }

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
    pub(in crate::execute) fn resolve_callable_fn_set(&mut self, function: &Obj) -> Option<FnSet> {
        match function {
            Obj::FunctionSpace(FunctionSpace::AnonymousFn(anon)) => Some(anon.body.clone()),
            Obj::FnObj(fo) if fo.body.is_empty() => match fo.head.as_ref() {
                FnObjHead::Object(obj) => self.resolve_callable_fn_set(obj),
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

    // Each field uses the selected carrier's actual arguments, e.g. Op<R>.add
    // has domain R, not the free parameter from struct Op<A>.
    pub(in crate::execute) fn resolve_field_access_field_type(
        &mut self,
        access: &FieldAccess,
    ) -> Option<Obj> {
        if access.fields.is_empty() {
            return None;
        }
        let mut carrier = self.resolve_definition_struct_carrier(access.obj.as_ref())?;
        let mut receiver = access.obj.as_ref().clone();
        for (index, field_name) in access.fields.iter().enumerate() {
            let field_type = self.instantiate_struct_field_type(&receiver, &carrier, field_name)?;
            let is_last = index + 1 == access.fields.len();
            if is_last {
                return Some(field_type);
            }
            match field_type {
                Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::StructObj(next)) => {
                    carrier = next;
                }
                _ => return None,
            }
            receiver =
                Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::FieldAccess(FieldAccess {
                    obj: access.obj.clone(),
                    fields: access.fields[..=index].to_vec(),
                }));
        }
        None
    }

    pub(super) fn instantiate_struct_field_type(
        &mut self,
        receiver: &Obj,
        carrier: &StructObj,
        field_name: &str,
    ) -> Option<Obj> {
        let def = self.def_struct_visible(&carrier.name)?;
        let field_type = def
            .fields
            .iter()
            .find(|field| field.binding.name == field_name)?
            .field_type
            .clone();
        // Keep parameter and dependent-field substitution identical to the
        // existing explicit release path; this does not release any facts.
        let subst = self.struct_release_subst(receiver, carrier, def).ok()?;
        self.inst_obj(&field_type, &subst).ok()
    }
}

// Head object for a FnObj (used when looking up InFunctionSet / field type).
pub(super) fn fn_obj_head_as_obj(head: &FnObjHead) -> Obj {
    match head {
        FnObjHead::Object(obj) => obj.as_ref().clone(),
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

// FnSet / AnonymousFn obj carriers must be fixed sets: no group's
// `param_type` may freely mention any binder of the same signature.
// Example reject: `fn(x R, y S(x))`.
//
// Why forall may look similar but is allowed: `forall S set, x S` uses binder
// *kinds* on TypedParameterList (`ParamType::Set`, then `Obj(S)`). That is a
// telescope over "introduce a set, then an element of it", not a function
// domain object. A set-theoretic function signature must fix each ordinary
// domain set up front, so SetBoundParameterList forbids the same dependence.
// Kind telescopes stay on introduce_typed_parameters (sequential). Return sets
// obey the fixed-carrier rule too; only `: dom_facts` and bodies cite parameters.
//
// Returns the failing group index when a citation is found.
pub(super) fn set_bound_param_type_cites_binder(list: &SetBoundParameterList) -> Option<usize> {
    for (index, group) in list.groups.iter().enumerate() {
        if fn_carrier_parameter_reference(group.param_type.as_ref(), list).is_some() {
            return Some(index);
        }
    }
    None
}

// Domains and the complete return object must be closed over the signature's
// own parameters, including references nested in another fn or set builder.
pub(super) fn fn_carrier_parameter_reference(
    carrier: &Obj,
    params: &SetBoundParameterList,
) -> Option<String> {
    let mut free = HashSet::new();
    collect_free_plain_ids(carrier, &HashSet::new(), &mut free);
    for group in &params.groups {
        for param in &group.params {
            if free.contains(&param.id) {
                return Some(param.name.clone());
            }
        }
    }
    None
}
