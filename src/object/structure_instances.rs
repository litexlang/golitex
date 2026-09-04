//! Structure instances, field access, and template instances.

use crate::prelude::*;

#[derive(Clone)]
pub struct StructObj {
    pub name: AtomicName,
    pub params: Vec<Obj>,
}

#[derive(Clone)]
pub struct ObjAsStructInstanceWithFieldAccess {
    pub obj: Box<Obj>,
    pub field_name: String,
    /// Filled by execution/instantiation, never by parsing. It preserves the
    /// field owner when substituting a typed receiver with an arbitrary value.
    pub resolved_struct_carrier: Option<Box<StructObj>>,
}

#[derive(Clone)]
pub struct InstantiatedTemplateObj {
    pub template_name: AtomicName,
    pub args: Vec<Obj>,
}

impl StructObj {
    pub fn new(name: AtomicName, params: Vec<Obj>) -> Self {
        StructObj { name, params }
    }
}

impl ObjAsStructInstanceWithFieldAccess {
    pub fn new(obj: Obj, field_name: String) -> Self {
        ObjAsStructInstanceWithFieldAccess {
            obj: Box::new(obj),
            field_name,
            resolved_struct_carrier: None,
        }
    }

    pub fn new_resolved(obj: Obj, field_name: String, struct_obj: StructObj) -> Self {
        ObjAsStructInstanceWithFieldAccess {
            obj: Box::new(obj),
            field_name,
            resolved_struct_carrier: Some(Box::new(struct_obj)),
        }
    }
}

impl InstantiatedTemplateObj {
    pub fn new(template_name: AtomicName, args: Vec<Obj>) -> Self {
        InstantiatedTemplateObj {
            template_name,
            args,
        }
    }

    pub fn surface_name(&self) -> String {
        format!(
            "{}{}{}{}{}",
            TEMPLATE_INSTANCE_PREFIX,
            self.template_name,
            LESS,
            vec_to_string_join_by_comma(&self.args),
            GREATER
        )
    }

}
