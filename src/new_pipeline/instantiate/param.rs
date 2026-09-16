use crate::new_pipeline::ast::param::{ParamType, SetBoundParameterList, TypedParameterList};

use super::InstCtx;
use super::error::InstError;

pub fn inst_param_type(ctx: &mut InstCtx<'_>, param_type: &ParamType) -> Result<ParamType, InstError> {
    match param_type {
        ParamType::Set(s) => Ok(ParamType::Set(s.clone())),
        ParamType::NonemptySet(s) => Ok(ParamType::NonemptySet(s.clone())),
        ParamType::FiniteSet(s) => Ok(ParamType::FiniteSet(s.clone())),
        ParamType::Obj(obj) => Ok(ParamType::Obj(ctx.inst_obj(obj)?)),
    }
}

pub fn inst_typed_parameter_list(
    ctx: &mut InstCtx<'_>,
    list: &TypedParameterList,
) -> Result<TypedParameterList, InstError> {
    let mut groups = Vec::with_capacity(list.groups.len());
    for group in &list.groups {
        groups.push(crate::new_pipeline::ast::param::TypedParameterGroup {
            params: group.params.clone(),
            param_type: inst_param_type(ctx, &group.param_type)?,
        });
    }
    Ok(TypedParameterList { groups })
}

pub fn inst_set_bound_parameter_list(
    ctx: &mut InstCtx<'_>,
    list: &SetBoundParameterList,
) -> Result<SetBoundParameterList, InstError> {
    let mut groups = Vec::with_capacity(list.groups.len());
    for group in &list.groups {
        groups.push(crate::new_pipeline::ast::param::SetBoundParameterGroup {
            params: group.params.clone(),
            param_type: Box::new(ctx.inst_obj(&group.param_type)?),
        });
    }
    Ok(SetBoundParameterList { groups })
}

pub fn typed_param_names(list: &TypedParameterList) -> Vec<String> {
    let mut names = Vec::new();
    for group in &list.groups {
        for param in &group.params {
            names.push(param.name.clone());
        }
    }
    names
}

pub fn inst_typed_parameter_list_under_binders(
    ctx: &mut InstCtx<'_>,
    list: &TypedParameterList,
) -> Result<TypedParameterList, InstError> {
    let names = typed_param_names(list);
    let binders = super::capture::prepare_binders(&names, &ctx.subst, &mut ctx.fresh_counter);
    super::capture::with_shadowed_binders(ctx, &binders, |ctx| inst_typed_parameter_list(ctx, list))
}
