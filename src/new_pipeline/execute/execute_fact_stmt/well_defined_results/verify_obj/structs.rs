//! Struct / template / field-access object WD.

use super::fail_to_verify_obj_well_defined::{
    FailToVerifyFieldAccessObjWellDefined, FailToVerifyInstantiatedTemplateObjObjWellDefined,
    FailToVerifyObjWellDefinedByDefCommon, FailToVerifyObjWellDefinedResult,
    FailToVerifyStructObjObjWellDefined,
};
use super::obj_well_defined_by_def_common::ObjWellDefinedByDefCommonStages;
use super::wrap_obj_well_defined_by_def::finish_by_def;
use super::entry::{ObjWellDefinedProof, VerifyObjWellDefinedResult};
use crate::new_pipeline::ast::fact::{
    AtomicFact, EqualFact, Fact, InFact, IsFiniteSetFact, IsNonemptySetFact, IsSetFact,
};
use crate::new_pipeline::ast::obj::{FieldAccess, InstantiatedTemplateObj, Obj, StructObj};
use crate::new_pipeline::ast::param::ParamType;
use crate::new_pipeline::ast::stmt::TemplateDefEnum;
use crate::new_pipeline::exec_env::exec_env::SpecialObjProperty;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::runtime_ids::IdentifierId;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};
use std::collections::HashMap;

impl Runtime {
    // `&Name` / `&Name<args>`: known structure definition, matching arity, param WD.
    // Does not prove membership `$in &Struct`.
    // Example: after `struct Point: x R; y R`, WD of `&Point` succeeds.
    pub(super) fn verify_struct_obj_well_definedness(
        &mut self,
        value: &StructObj,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyObjWellDefinedResult> {
        let plain = value.name.local_name();
        let expected_arity = {
            let Some(def) = self.def_struct_visible_in_stack(plain) else {
                return Ok(VerifyObjWellDefinedResult::Failed(
                    FailToVerifyObjWellDefinedResult::StructObj(
                        FailToVerifyStructObjObjWellDefined(
                            FailToVerifyObjWellDefinedByDefCommon::Others(format!(
                                "struct `{plain}` is not defined"
                            )),
                        ),
                    ),
                ));
            };
            match &def.param_def_with_dom {
                None => 0,
                Some((params, _)) => params.ordered_param_ids().len(),
            }
        };
        if value.params.len() != expected_arity {
            return Ok(VerifyObjWellDefinedResult::Failed(
                FailToVerifyObjWellDefinedResult::StructObj(FailToVerifyStructObjObjWellDefined(
                    FailToVerifyObjWellDefinedByDefCommon::Others(format!(
                        "struct `{plain}` expects {expected_arity} parameter(s), got {}",
                        value.params.len()
                    )),
                )),
            ));
        }

        let refs: Vec<&Obj> = value.params.iter().collect();
        let stages = self.verify_objs_as_children(&refs, verify_state.clone())?;
        let root = Obj::StructObj(value.clone());
        match finish_by_def(&root, stages) {
            Ok(by_def) => {
                if verify_state.store_well_defined_fact {
                    let wd_id = self.ids.allocate_well_definedness_id();
                    self.top_exec_env_mut()
                        .well_defined_objects
                        .record(root, wd_id);
                }
                Ok(VerifyObjWellDefinedResult::Success(ObjWellDefinedProof::ByDef(
                    by_def,
                )))
            }
            Err(fail) => Ok(VerifyObjWellDefinedResult::Failed(fail)),
        }
    }

    // `x.y` / `x.y.z`: receiver WD, then walk `fields` on the definition-time carrier.
    // Intermediate fields (all but the last) must themselves have `&Struct` type.
    // Example: after `forall p &Point:`, WD of `p.x` succeeds.
    pub(super) fn verify_field_access_obj_well_definedness(
        &mut self,
        value: &FieldAccess,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyObjWellDefinedResult> {
        if value.fields.is_empty() {
            return Ok(field_access_fail(
                "field access expects at least one field name".to_string(),
            ));
        }

        let receiver_wd =
            self.verify_obj_well_definedness(value.obj.as_ref(), verify_state.clone())?;
        if receiver_wd.is_failed() {
            return Ok(VerifyObjWellDefinedResult::Failed(
                FailToVerifyObjWellDefinedResult::FieldAccess(FailToVerifyFieldAccessObjWellDefined(
                    FailToVerifyObjWellDefinedByDefCommon::Child {
                        obj: value.obj.as_ref().clone(),
                        child: Box::new(match receiver_wd {
                            VerifyObjWellDefinedResult::Failed(reason) => reason,
                            VerifyObjWellDefinedResult::Success(_) => unreachable!(),
                        }),
                    },
                )),
            ));
        }

        let Some(mut carrier) = self.resolve_definition_struct_carrier(value.obj.as_ref()) else {
            return Ok(field_access_fail(format!(
                "object has no definition-time struct carrier for field `{}`",
                value.fields.join(".")
            )));
        };

        for (index, field_name) in value.fields.iter().enumerate() {
            let plain = carrier.name.local_name().to_string();
            let Some(def) = self.def_struct_visible_in_stack(&plain) else {
                return Ok(field_access_fail(format!(
                    "struct `{plain}` is not defined"
                )));
            };
            let Some(field_def) = def.fields.iter().find(|f| f.binding.name == *field_name) else {
                return Ok(field_access_fail(format!(
                    "struct `{plain}` has no field `{field_name}`"
                )));
            };
            let is_last = index + 1 == value.fields.len();
            if is_last {
                break;
            }
            match &field_def.field_type {
                Obj::StructObj(next) => carrier = next.clone(),
                _ => {
                    return Ok(field_access_fail(format!(
                        "field `{field_name}` of struct `{plain}` is not a struct carrier"
                    )));
                }
            }
        }

        let stages = ObjWellDefinedByDefCommonStages::from_children(vec![(
            value.obj.as_ref().clone(),
            receiver_wd,
        )]);
        let root = Obj::FieldAccess(value.clone());
        match finish_by_def(&root, stages) {
            Ok(by_def) => {
                if verify_state.store_well_defined_fact {
                    let wd_id = self.ids.allocate_well_definedness_id();
                    self.top_exec_env_mut()
                        .well_defined_objects
                        .record(root, wd_id);
                }
                Ok(VerifyObjWellDefinedResult::Success(ObjWellDefinedProof::ByDef(
                    by_def,
                )))
            }
            Err(fail) => Ok(VerifyObjWellDefinedResult::Failed(fail)),
        }
    }

    // Definition-time `DefinedAsStruct` only (exact ObjIR; not equality class).
    // Nested field access: walk all fields; result carrier is the last field's
    // type when that type is `&Struct`.
    pub(super) fn resolve_definition_struct_carrier(&self, obj: &Obj) -> Option<StructObj> {
        if let Some(carrier) = self.defined_as_struct_visible_in_stack(obj) {
            return Some(carrier);
        }
        let Obj::FieldAccess(access) = obj else {
            return None;
        };
        if access.fields.is_empty() {
            return None;
        }
        let mut carrier = self.resolve_definition_struct_carrier(access.obj.as_ref())?;
        for (index, field_name) in access.fields.iter().enumerate() {
            let def = self.def_struct_visible_in_stack(carrier.name.local_name())?;
            let field = def.fields.iter().find(|f| f.binding.name == *field_name)?;
            let is_last = index + 1 == access.fields.len();
            match &field.field_type {
                Obj::StructObj(next) => {
                    if is_last {
                        return Some(next.clone());
                    }
                    carrier = next.clone();
                }
                _ => {
                    if is_last {
                        return None;
                    }
                    return None;
                }
            }
        }
        None
    }

    pub(super) fn defined_as_struct_visible_in_stack(&self, obj: &Obj) -> Option<StructObj> {
        let key = obj.ir();
        for env in self.execution_environments_stack.iter().rev() {
            let Some(props) = env.special_object_properties.get(&key) else {
                continue;
            };
            for prop in props {
                if let SpecialObjProperty::DefinedAsStruct((carrier, _)) = prop {
                    return Some(carrier.clone());
                }
            }
        }
        None
    }

    // `\Name<args>`: known template, matching arity, args WD, param-type + domain obligations.
    // Surface stays InstantiatedTemplateObj (no materialization).
    // Example: after `template<S set>: have carrier_copy set = S`, WD of `\carrier_copy<R>`.
    pub(super) fn verify_instantiated_template_obj_well_definedness(
        &mut self,
        value: &InstantiatedTemplateObj,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyObjWellDefinedResult> {
        let plain = value.template_name.local_name();
        let (expected_arity, param_groups, dom_facts) = {
            let Some(def) = self.def_template_visible_in_stack(plain) else {
                return Ok(template_fail(FailToVerifyObjWellDefinedByDefCommon::Others(
                    format!("template `{plain}` is not defined"),
                )));
            };
            (
                def.template_arg_def.ordered_param_ids().len(),
                def.template_arg_def.groups.clone(),
                def.template_arg_dom.clone(),
            )
        };
        if value.args.len() != expected_arity {
            return Ok(template_fail(FailToVerifyObjWellDefinedByDefCommon::Others(
                format!(
                    "template `{plain}` expects {expected_arity} argument(s), got {}",
                    value.args.len()
                ),
            )));
        }

        let mut stages = ObjWellDefinedByDefCommonStages::leaf();
        for arg in &value.args {
            let child = self.verify_obj_well_definedness(arg, verify_state.clone())?;
            let failed = child.is_failed();
            stages.child_obj_well_defined.push((arg.clone(), child));
            if failed {
                let root = Obj::InstantiatedTemplateObj(value.clone());
                return Ok(match finish_by_def(&root, stages) {
                    Ok(_) => unreachable!(),
                    Err(fail) => VerifyObjWellDefinedResult::Failed(fail),
                });
            }
        }

        let param_ids = {
            let mut ids = Vec::with_capacity(expected_arity);
            for group in &param_groups {
                for param in &group.params {
                    ids.push(param.id);
                }
            }
            ids
        };
        let mut subst: HashMap<IdentifierId, Obj> = HashMap::new();
        for (id, arg) in param_ids.iter().zip(value.args.iter()) {
            subst.insert(*id, arg.clone());
        }

        let mut arg_index = 0;
        for group in &param_groups {
            let param_type = match self.inst_param_type(&group.param_type, &subst) {
                Ok(param_type) => param_type,
                Err(_) => {
                    return Ok(template_fail(FailToVerifyObjWellDefinedByDefCommon::Others(
                        format!("template `{plain}`: failed to instantiate parameter type"),
                    )));
                }
            };
            for _param in &group.params {
                let arg = &value.args[arg_index];
                let type_fact = type_fact_for_instantiated_template_arg(
                    arg.clone(),
                    &param_type,
                    self.ids.allocate_fact_id(),
                );
                let req = self.verify_fact(&type_fact, verify_state.clone())?;
                let failed = req.is_failed();
                stages.requirement_fact_verified.push(req);
                if failed {
                    let root = Obj::InstantiatedTemplateObj(value.clone());
                    return Ok(match finish_by_def(&root, stages) {
                        Ok(_) => unreachable!(),
                        Err(fail) => VerifyObjWellDefinedResult::Failed(fail),
                    });
                }
                arg_index += 1;
            }
        }

        for dom in &dom_facts {
            let instantiated = match self.inst_quantifier_free_fact(dom, &subst) {
                Ok(f) => f,
                Err(_) => {
                    return Ok(template_fail(FailToVerifyObjWellDefinedByDefCommon::Others(
                        format!("template `{plain}`: failed to instantiate domain fact"),
                    )));
                }
            };
            let req =
                self.verify_required_quantifier_free_fact(instantiated, verify_state.clone())?;
            let failed = req.is_failed();
            stages.requirement_fact_verified.push(req);
            if failed {
                let root = Obj::InstantiatedTemplateObj(value.clone());
                return Ok(match finish_by_def(&root, stages) {
                    Ok(_) => unreachable!(),
                    Err(fail) => VerifyObjWellDefinedResult::Failed(fail),
                });
            }
        }

        let root = Obj::InstantiatedTemplateObj(value.clone());
        match finish_by_def(&root, stages) {
            Ok(by_def) => {
                if verify_state.store_well_defined_fact {
                    let wd_id = self.ids.allocate_well_definedness_id();
                    self.top_exec_env_mut()
                        .well_defined_objects
                        .record(root.clone(), wd_id);
                    // Have-fn template bodies: register the surface as callable so
                    // `\T<a>(x)` reuses ordinary InFunctionSet application WD.
                    // Have-obj bodies: store `\T<a> = subst(rhs)` for definitional use.
                    self.maybe_register_instantiated_template_definitional_facts(value)?;
                }
                Ok(VerifyObjWellDefinedResult::Success(ObjWellDefinedProof::ByDef(
                    by_def,
                )))
            }
            Err(fail) => Ok(VerifyObjWellDefinedResult::Failed(fail)),
        }
    }

    // After WD of `\Name<args>`, store definitional facts for supported bodies:
    // - have fn: `\Name<args> $in inst(FnSet)` and `\Name<args> = inst(anon)`
    // - have =: `\Name<args> = subst(rhs)`
    fn maybe_register_instantiated_template_definitional_facts(
        &mut self,
        value: &InstantiatedTemplateObj,
    ) -> RuntimeResult<()> {
        let plain = value.template_name.local_name();
        let Some(def) = self.def_template_visible_in_stack(plain).cloned() else {
            return Ok(());
        };
        match &def.template_def_stmt {
            TemplateDefEnum::HaveFnEqualStmt(have_fn) => {
                let mut subst: HashMap<IdentifierId, Obj> = HashMap::new();
                for (id, arg) in def
                    .template_arg_def
                    .ordered_param_ids()
                    .into_iter()
                    .zip(value.args.iter())
                {
                    subst.insert(id, arg.clone());
                }
                let Ok(anon) = self.inst_obj(
                    &Obj::AnonymousFn(have_fn.equal_to_anonymous_fn.clone()),
                    &subst,
                ) else {
                    return Ok(());
                };
                let Obj::AnonymousFn(anon) = anon else {
                    return Ok(());
                };
                let surface = Obj::InstantiatedTemplateObj(value.clone());
                let membership = Fact::AtomicFact(AtomicFact::InFact(InFact {
                    fact_id: self.ids.allocate_fact_id(),
                    element: surface.clone(),
                    set: Obj::FnSet(anon.body.clone()),
                    line_file: None,
                }));
                self.store_fact_and_infer(&membership)?;
                let defining_equal = Fact::AtomicFact(AtomicFact::EqualFact(EqualFact {
                    fact_id: self.ids.allocate_fact_id(),
                    left: surface,
                    right: Obj::AnonymousFn(anon),
                    line_file: None,
                }));
                self.store_fact_and_infer(&defining_equal)?;
            }
            TemplateDefEnum::HaveObjEqualStmt(_) => {
                let Some(expanded_rhs) =
                    self.expanded_have_obj_equal_rhs_of_instantiated_template(value)?
                else {
                    return Ok(());
                };
                let surface = Obj::InstantiatedTemplateObj(value.clone());
                let defining_equal = Fact::AtomicFact(AtomicFact::EqualFact(EqualFact {
                    fact_id: self.ids.allocate_fact_id(),
                    left: surface,
                    right: expanded_rhs,
                    line_file: None,
                }));
                self.store_fact_and_infer(&defining_equal)?;
            }
            _ => {}
        }
        Ok(())
    }
}

fn template_fail(common: FailToVerifyObjWellDefinedByDefCommon) -> VerifyObjWellDefinedResult {
    VerifyObjWellDefinedResult::Failed(FailToVerifyObjWellDefinedResult::InstantiatedTemplateObj(
        FailToVerifyInstantiatedTemplateObjObjWellDefined(common),
    ))
}

fn field_access_fail(message: String) -> VerifyObjWellDefinedResult {
    VerifyObjWellDefinedResult::Failed(FailToVerifyObjWellDefinedResult::FieldAccess(
        FailToVerifyFieldAccessObjWellDefined(FailToVerifyObjWellDefinedByDefCommon::Others(
            message,
        )),
    ))
}

// Same shapes as forall instantiation param-type obligations.
fn type_fact_for_instantiated_template_arg(
    arg: Obj,
    param_type: &ParamType,
    fact_id: crate::new_pipeline::runtime::FactId,
) -> Fact {
    match param_type {
        ParamType::Obj(param_set) => Fact::AtomicFact(AtomicFact::InFact(InFact {
            fact_id,
            element: arg,
            set: param_set.clone(),
            line_file: None,
        })),
        ParamType::Set(_) => Fact::AtomicFact(AtomicFact::IsSetFact(IsSetFact {
            fact_id,
            set: arg,
            line_file: None,
        })),
        ParamType::NonemptySet(_) => {
            Fact::AtomicFact(AtomicFact::IsNonemptySetFact(IsNonemptySetFact {
                fact_id,
                set: arg,
                line_file: None,
            }))
        }
        ParamType::FiniteSet(_) => Fact::AtomicFact(AtomicFact::IsFiniteSetFact(IsFiniteSetFact {
            fact_id,
            set: arg,
            line_file: None,
        })),
    }
}
