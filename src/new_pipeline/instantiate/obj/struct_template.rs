use crate::new_pipeline::ast::obj::{
    InstantiatedTemplateObj, IntervalObj, IntervalObjStruct, Obj,
    ObjAsStructInstanceWithFieldAccess, OneSideInfinityIntervalObj,
    OneSideInfinityIntervalObjStruct, StructObj,
};

use super::super::InstCtx;
use super::super::error::InstError;

pub fn inst_struct_obj(ctx: &mut InstCtx<'_>, s: &StructObj) -> Result<StructObj, InstError> {
    let mut params = Vec::with_capacity(s.params.len());
    for o in &s.params {
        params.push(ctx.inst_obj(o)?);
    }
    Ok(StructObj {
        name: s.name.clone(),
        params,
    })
}

pub fn inst_obj_as_struct(
    ctx: &mut InstCtx<'_>,
    a: &ObjAsStructInstanceWithFieldAccess,
) -> Result<ObjAsStructInstanceWithFieldAccess, InstError> {
    let carrier = match &a.resolved_struct_carrier {
        None => return Err(InstError::MissingStructCarrier),
        Some(c) => Some(Box::new(inst_struct_obj(ctx, c)?)),
    };
    Ok(ObjAsStructInstanceWithFieldAccess {
        obj: Box::new(ctx.inst_obj(&a.obj)?),
        field_name: a.field_name.clone(),
        resolved_struct_carrier: carrier,
    })
}

pub fn inst_instantiated_template(
    ctx: &mut InstCtx<'_>,
    a: &InstantiatedTemplateObj,
) -> Result<InstantiatedTemplateObj, InstError> {
    let mut args = Vec::with_capacity(a.args.len());
    for o in &a.args {
        args.push(ctx.inst_obj(o)?);
    }
    Ok(InstantiatedTemplateObj {
        template_name: a.template_name.clone(),
        args,
    })
}

pub fn inst_one_side_infinity_interval(
    ctx: &mut InstCtx<'_>,
    i: &OneSideInfinityIntervalObj,
) -> Result<Obj, InstError> {
    let mut inst_struct = |s: &OneSideInfinityIntervalObjStruct| {
        Ok(OneSideInfinityIntervalObjStruct {
            start: Box::new(ctx.inst_obj(&s.start)?),
        })
    };
    Ok(match i {
        OneSideInfinityIntervalObj::LeftOpen(s) => {
            Obj::OneSideInfinityIntervalObj(OneSideInfinityIntervalObj::LeftOpen(inst_struct(s)?))
        }
        OneSideInfinityIntervalObj::LeftClosed(s) => Obj::OneSideInfinityIntervalObj(
            OneSideInfinityIntervalObj::LeftClosed(inst_struct(s)?),
        ),
        OneSideInfinityIntervalObj::RightOpen(s) => {
            Obj::OneSideInfinityIntervalObj(OneSideInfinityIntervalObj::RightOpen(inst_struct(s)?))
        }
        OneSideInfinityIntervalObj::RightClosed(s) => Obj::OneSideInfinityIntervalObj(
            OneSideInfinityIntervalObj::RightClosed(inst_struct(s)?),
        ),
    })
}

pub fn inst_interval(ctx: &mut InstCtx<'_>, i: &IntervalObj) -> Result<Obj, InstError> {
    let mut inst_struct = |s: &IntervalObjStruct| {
        Ok(IntervalObjStruct {
            start: Box::new(ctx.inst_obj(&s.start)?),
            end: Box::new(ctx.inst_obj(&s.end)?),
        })
    };
    Ok(match i {
        IntervalObj::LeftOpenRightOpen(s) => {
            Obj::IntervalObj(IntervalObj::LeftOpenRightOpen(inst_struct(s)?))
        }
        IntervalObj::LeftOpenRightClosed(s) => {
            Obj::IntervalObj(IntervalObj::LeftOpenRightClosed(inst_struct(s)?))
        }
        IntervalObj::LeftClosedRightOpen(s) => {
            Obj::IntervalObj(IntervalObj::LeftClosedRightOpen(inst_struct(s)?))
        }
        IntervalObj::LeftClosedRightClosed(s) => {
            Obj::IntervalObj(IntervalObj::LeftClosedRightClosed(inst_struct(s)?))
        }
    })
}
