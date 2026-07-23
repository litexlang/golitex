use super::*;

pub(crate) fn general_cart_member_fn_set(
    runtime: &Runtime,
    general_cart: &GeneralCart,
) -> Result<Obj, RuntimeError> {
    let param_name = runtime.generate_internal_binder_name();
    Ok(FnSet::new(
        vec![runtime.fresh_param_group_with_set(
            vec![param_name],
            general_cart.index_set.as_ref().clone(),
        )?],
        vec![],
        BigUnion::new(general_cart.family_set.as_ref().clone()).into(),
    )?
    .into())
}

pub(crate) fn general_cart_member_pointwise_fact(
    runtime: &Runtime,
    general_cart: &GeneralCart,
    member: &Obj,
    line_file: &LineFile,
) -> Result<Option<Fact>, RuntimeError> {
    let Some(member_head) = FnObjHead::from_callable_obj(member.clone()) else {
        return Ok(None);
    };
    let Some(family_head) = FnObjHead::from_callable_obj(general_cart.family_fn.as_ref().clone())
    else {
        return Ok(None);
    };
    let param_name = runtime.generate_internal_binder_name();
    let param_group = runtime.fresh_param_group_with_type(
        vec![param_name],
        ParamType::Obj(general_cart.index_set.as_ref().clone()),
    )?;
    let param_obj = obj_for_bound_param_in_scope(&param_group.params[0], ParamObjType::Forall);
    let member_at_param: Obj =
        FnObj::new(member_head, vec![vec![Box::new(param_obj.clone())]]).into();
    let family_at_param: Obj =
        FnObj::new(family_head, vec![vec![Box::new(param_obj.clone())]]).into();
    Ok(Some(
        ForallFact::new(
            ParamDefWithType::new(vec![param_group]),
            vec![],
            vec![InFact::new(member_at_param, family_at_param, line_file.clone()).into()],
            line_file.clone(),
        )?
        .into(),
    ))
}
