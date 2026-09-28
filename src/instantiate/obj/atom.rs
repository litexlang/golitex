use std::collections::HashMap;

use crate::ast::obj::{IdentifierObj, Obj};
use crate::runtime::runtime_ids::IdentifierId;
use crate::runtime::Runtime;

use super::super::error::InstError;

impl Runtime {
    pub(crate) fn inst_identifier_obj(
        &mut self,
        obj: &Obj,
        param_to_arg_map: &HashMap<IdentifierId, Obj>,
    ) -> Result<Obj, InstError> {
        let Obj::Identifier(id) = obj else {
            return Ok(obj.clone());
        };
        match id {
            IdentifierObj::Plain { id, .. } => {
                if let Some(replacement) = param_to_arg_map.get(id) {
                    return Ok(replacement.clone());
                }
            }
            IdentifierObj::WithExportFileId { .. }
            | IdentifierObj::WithModAndExportFileId { .. } => {}
        }
        Ok(obj.clone())
    }

    pub(crate) fn inst_leaf_obj(obj: &Obj) -> Obj {
        obj.clone()
    }
}
