//! Struct / template object WD (children only until P3).

use super::obj_well_defined_by_def_common::ObjWellDefinedByDefCommonStages;
use crate::new_pipeline::ast::obj::{
    InstantiatedTemplateObj, Obj, ObjAsStructInstanceWithFieldAccess, StructObj,
};
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

impl Runtime {
    pub(super) fn verify_struct_obj_well_definedness_by_def(
        &mut self,
        value: &StructObj,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        let refs: Vec<&Obj> = value.params.iter().collect();
        self.verify_objs_as_children(&refs, verify_state)
    }

    pub(super) fn verify_obj_as_struct_instance_with_field_access_obj_well_definedness_by_def(
        &mut self,
        value: &ObjAsStructInstanceWithFieldAccess,
        verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedByDefCommonStages> {
        let mut children = Vec::new();
        children.push(value.obj.as_ref());
        if let Some(carrier) = &value.resolved_struct_carrier {
            for param in &carrier.params {
                children.push(param);
            }
        }
        self.verify_objs_as_children(&children, verify_state)
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
