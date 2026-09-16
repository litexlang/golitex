use std::collections::HashMap;

use crate::new_pipeline::ast::names::AtomicName;
use crate::new_pipeline::ast::obj::Obj;
use crate::new_pipeline::runtime::Runtime;

use super::super::error::InstError;

impl Runtime {
    pub(crate) fn inst_identifier_obj(
        &mut self,
        obj: &Obj,
        param_to_arg_map: &HashMap<String, Obj>,
        _fresh: &mut u64,
        binder_renames: &HashMap<String, String>,
    ) -> Result<Obj, InstError> {
        let Obj::Identifier(id) = obj else {
            return Ok(obj.clone());
        };
        if let AtomicName::Plain { name } = &id.name {
            if let Some(binder_name) = binder_renames.get(name) {
                return Ok(Obj::Identifier(crate::new_pipeline::ast::obj::IdentifierObj::plain(
                    binder_name.clone(),
                )));
            }
            if let Some(replacement) = param_to_arg_map.get(name) {
                return Ok(replacement.clone());
            }
        }
        Ok(obj.clone())
    }

    pub(crate) fn inst_leaf_obj(obj: &Obj) -> Obj {
        obj.clone()
    }
}
