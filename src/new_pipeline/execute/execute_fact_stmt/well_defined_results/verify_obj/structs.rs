//! Struct / template / field-access object WD.

use super::fail_to_verify_obj_well_defined::{
    FailToVerifyFieldAccessObjWellDefined, FailToVerifyObjWellDefinedByDefCommon,
    FailToVerifyObjWellDefinedResult, FailToVerifyStructObjObjWellDefined,
};
use super::obj_well_defined_by_def_common::ObjWellDefinedByDefCommonStages;
use super::wrap_obj_well_defined_by_def::finish_by_def;
use super::entry::{ObjWellDefinedProof, VerifyObjWellDefinedResult};
use crate::new_pipeline::ast::obj::{FieldAccess, InstantiatedTemplateObj, Obj, StructObj};
use crate::new_pipeline::exec_env::exec_env::SpecialObjProperty;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

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
            let Some(field_def) = def.fields.iter().find(|f| f.binding == *field_name) else {
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
            let field = def.fields.iter().find(|f| f.binding == *field_name)?;
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

    pub(super) fn verify_instantiated_template_obj_well_definedness_by_def(
        &mut self,
        value: &InstantiatedTemplateObj,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        let refs: Vec<&Obj> = value.args.iter().collect();
        self.verify_objs_as_children(&refs, verify_state)
    }
}

fn field_access_fail(message: String) -> VerifyObjWellDefinedResult {
    VerifyObjWellDefinedResult::Failed(FailToVerifyObjWellDefinedResult::FieldAccess(
        FailToVerifyFieldAccessObjWellDefined(FailToVerifyObjWellDefinedByDefCommon::Others(
            message,
        )),
    ))
}
