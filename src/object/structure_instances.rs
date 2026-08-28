//! Structure instances, field access, and template instances.

use crate::prelude::*;

#[derive(Clone)]
pub struct StructObj {
    pub name: AtomicName,
    pub params: Vec<Obj>,
}

#[derive(Clone)]
pub struct ObjAsStructInstanceWithFieldAccess {
    pub struct_obj: Box<StructObj>,
    pub obj: Box<Obj>,
    pub field_name: String,
}

#[derive(Clone)]
pub struct InstantiatedTemplateObj {
    pub template_name: AtomicName,
    pub args: Vec<Obj>,
    pub symbol: SymbolRef,
}

impl StructObj {
    pub fn new(name: AtomicName, params: Vec<Obj>) -> Self {
        StructObj { name, params }
    }
}

impl ObjAsStructInstanceWithFieldAccess {
    pub fn new(struct_obj: StructObj, obj: Obj, field_name: String) -> Self {
        ObjAsStructInstanceWithFieldAccess {
            struct_obj: Box::new(struct_obj),
            obj: Box::new(obj),
            field_name,
        }
    }
}

impl InstantiatedTemplateObj {
    pub fn new(template_name: AtomicName, args: Vec<Obj>, symbol: SymbolRef) -> Self {
        InstantiatedTemplateObj {
            template_name,
            args,
            symbol,
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

    pub fn definition_binding(&self) -> SymbolBinding {
        SymbolBinding::new(
            self.symbol.id(),
            self.surface_name(),
            self.symbol.display_name().to_string(),
        )
    }
}
