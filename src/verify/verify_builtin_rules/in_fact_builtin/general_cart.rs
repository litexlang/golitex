use super::*;

pub(crate) fn general_cart_member_fn_set(general_cart: &GeneralCart) -> Result<Obj, RuntimeError> {
    Ok(FnSet::new(
        vec![ParamGroupWithSet::new(
            vec!["t".to_string()],
            general_cart.index_set.as_ref().clone(),
        )],
        vec![],
        Cup::new(general_cart.family_set.as_ref().clone()).into(),
    )?
    .into())
}

pub(crate) fn general_cart_member_pointwise_fact(
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
    let param_name = "t".to_string();
    let param_obj = obj_for_bound_param_in_scope(param_name.clone(), ParamObjType::Forall);
    let member_at_param: Obj =
        FnObj::new(member_head, vec![vec![Box::new(param_obj.clone())]]).into();
    let family_at_param: Obj =
        FnObj::new(family_head, vec![vec![Box::new(param_obj.clone())]]).into();
    Ok(Some(
        ForallFact::new(
            ParamDefWithType::new(vec![ParamGroupWithParamType::new(
                vec![param_name],
                ParamType::Obj(general_cart.index_set.as_ref().clone()),
            )]),
            vec![],
            vec![InFact::new(member_at_param, family_at_param, line_file.clone()).into()],
            line_file.clone(),
        )?
        .into(),
    ))
}
