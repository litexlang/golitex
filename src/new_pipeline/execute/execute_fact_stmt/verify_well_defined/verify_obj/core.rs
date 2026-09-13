//! Function / atom / standard-set object WD.

use super::entry::ObjWellDefinedProofByDef;
use crate::new_pipeline::ast::obj::{AnonymousFn, FnObj, FnObjHead, FnSet, Obj};
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

impl Runtime {
    pub(super) fn verify_atom_obj_well_definedness_by_def(
        &mut self, _verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        let _ = self;
        Ok(ObjWellDefinedProofByDef::leaf())
    }

    pub(super) fn verify_standard_set_obj_well_definedness_by_def(
        &mut self, _verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        let _ = self;
        Ok(ObjWellDefinedProofByDef::leaf())
    }

    pub(super) fn verify_fn_obj_well_definedness_by_def(
        &mut self, value: &FnObj, verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        let mut children = Vec::new();
        self.collect_fn_obj_head_child_objs(&value.head, &mut children);
        for layer in &value.body {
            for arg in layer {
                children.push(arg.as_ref());
            }
        }
        self.verify_objs_as_children(&children, verify_state)
    }

    fn collect_fn_obj_head_child_objs<'a>(
        &self, head: &'a FnObjHead, children: &mut Vec<&'a Obj>,
    ) {
        let _ = self;
        match head {
            FnObjHead::Identifier(_) | FnObjHead::IdentifierWithMod(_) | FnObjHead::Bound(_) => {}
            FnObjHead::AnonymousFnLiteral(anon) => {
                for group in &anon.body.set_bound_parameters.groups {
                    children.push(group.param_type.as_ref());
                }
                children.push(anon.body.ret_set.as_ref());
                children.push(anon.equal_to.as_ref());
            }
            FnObjHead::FiniteSeqListObj(list) => {
                for obj in &list.objs { children.push(obj.as_ref()); }
            }
            FnObjHead::ObjAtIndex(at) => {
                children.push(at.obj.as_ref());
                children.push(at.index.as_ref());
            }
            FnObjHead::ObjAsStructInstanceWithFieldAccess(access) => {
                children.push(access.obj.as_ref());
                if let Some(carrier) = &access.resolved_struct_carrier {
                    for param in &carrier.params { children.push(param); }
                }
            }
            FnObjHead::InstantiatedTemplateObj(inst) => {
                for arg in &inst.args { children.push(arg); }
            }
            FnObjHead::MatrixOperator(obj) => { children.push(obj.as_ref()); }
        }
    }

    pub(super) fn verify_fn_set_obj_well_definedness_by_def(
        &mut self, value: &FnSet, verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        let mut children = Vec::new();
        for group in &value.body.set_bound_parameters.groups {
            children.push(group.param_type.as_ref());
        }
        children.push(value.body.ret_set.as_ref());
        let _ = &value.body.dom_facts;
        self.verify_objs_as_children(&children, verify_state)
    }

    pub(super) fn verify_anonymous_fn_obj_well_definedness_by_def(
        &mut self, value: &AnonymousFn, verify_state: VerifyState,
    ) -> RuntimeResult<ObjWellDefinedProofByDef> {
        let mut children = Vec::new();
        for group in &value.body.set_bound_parameters.groups {
            children.push(group.param_type.as_ref());
        }
        children.push(value.body.ret_set.as_ref());
        children.push(value.equal_to.as_ref());
        let _ = &value.body.dom_facts;
        self.verify_objs_as_children(&children, verify_state)
    }
}
