use crate::new_pipeline::ast::names::AtomicName;
use crate::new_pipeline::ast::obj::Obj;

use super::super::InstCtx;
use super::super::error::InstError;
use super::super::mode::SubstitutionMode;

pub fn inst_identifier(ctx: &mut InstCtx<'_>, obj: &Obj) -> Result<Obj, InstError> {
    let Obj::Identifier(id) = obj else {
        return Ok(obj.clone());
    };
    match ctx.mode {
        SubstitutionMode::Exact => {
            if let AtomicName::Plain { name } = &id.name {
                if let Some(binder_name) = ctx.binder_renames.get(name) {
                    return Ok(Obj::Identifier(crate::new_pipeline::ast::obj::IdentifierObj::plain(
                        binder_name.clone(),
                    )));
                }
                if let Some(replacement) = ctx.subst.get(name) {
                    return Ok(replacement.clone());
                }
            }
            Ok(obj.clone())
        }
    }
}

pub fn inst_leaf(obj: &Obj) -> Obj {
    obj.clone()
}
