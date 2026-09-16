use crate::new_pipeline::ast::obj::{
    AnonymousFn, FnObj, FnObjHead, Obj,
    SetBuilder,
};

use super::super::InstCtx;
use super::super::capture;
use super::super::error::InstError;

pub fn inst_fn_obj_head(ctx: &mut InstCtx<'_>, head: &FnObjHead) -> Result<FnObjHead, InstError> {
    match head {
        FnObjHead::Identifier(id) => Ok(FnObjHead::Identifier(id.clone())),
        FnObjHead::AnonymousFnLiteral(af) => Ok(FnObjHead::AnonymousFnLiteral(Box::new(
            capture::inst_anonymous_fn(ctx, af)?,
        ))),
        FnObjHead::FiniteSeqListObj(a) => {
            Ok(FnObjHead::FiniteSeqListObj(super::set::inst_finite_seq_list_obj(
                ctx,
                a,
            )?.expect_finite_seq_list()))
        }
        FnObjHead::ObjAtIndex(a) => Ok(FnObjHead::ObjAtIndex(
            super::set::inst_obj_at_index(ctx, a)?.expect_obj_at_index(),
        )),
        FnObjHead::ObjAsStructInstanceWithFieldAccess(a) => Ok(
            FnObjHead::ObjAsStructInstanceWithFieldAccess(super::struct_template::inst_obj_as_struct(
                ctx, a,
            )?),
        ),
        FnObjHead::InstantiatedTemplateObj(a) => Ok(FnObjHead::InstantiatedTemplateObj(
            super::struct_template::inst_instantiated_template(ctx, a)?,
        )),
    }
}

pub fn inst_fn_obj(ctx: &mut InstCtx<'_>, f: &FnObj) -> Result<Obj, InstError> {
    let head = inst_fn_obj_head(ctx, f.head.as_ref())?;
    let mut body = Vec::with_capacity(f.body.len());
    for group in &f.body {
        let mut new_group = Vec::with_capacity(group.len());
        for o in group {
            new_group.push(Box::new(ctx.inst_obj(o)?));
        }
        body.push(new_group);
    }
    Ok(Obj::FnObj(FnObj {
        head: Box::new(head),
        body,
    }))
}

pub fn inst_set_builder(ctx: &mut InstCtx<'_>, sb: &SetBuilder) -> Result<Obj, InstError> {
    Ok(Obj::SetBuilder(capture::inst_set_builder(ctx, sb)?))
}

pub fn inst_fn_set(ctx: &mut InstCtx<'_>, fs: &crate::new_pipeline::ast::obj::FnSet) -> Result<Obj, InstError> {
    Ok(Obj::FnSet(capture::inst_fn_set(ctx, fs)?))
}

pub fn inst_anonymous_fn(ctx: &mut InstCtx<'_>, af: &AnonymousFn) -> Result<Obj, InstError> {
    Ok(Obj::AnonymousFn(capture::inst_anonymous_fn(ctx, af)?))
}

trait ObjExpect {
    fn expect_finite_seq_list(self) -> crate::new_pipeline::ast::obj::FiniteSeqListObj;
    fn expect_obj_at_index(self) -> crate::new_pipeline::ast::obj::ObjAtIndex;
}

impl ObjExpect for Obj {
    fn expect_finite_seq_list(self) -> crate::new_pipeline::ast::obj::FiniteSeqListObj {
        match self {
            Obj::FiniteSeqListObj(a) => a,
            _ => panic!("expected FiniteSeqListObj"),
        }
    }

    fn expect_obj_at_index(self) -> crate::new_pipeline::ast::obj::ObjAtIndex {
        match self {
            Obj::ObjAtIndex(a) => a,
            _ => panic!("expected ObjAtIndex"),
        }
    }
}
