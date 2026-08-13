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
        ForallFact::new_canonical_forall(
            ParamDefWithType::new(vec![param_group]),
            vec![],
            vec![InFact::new(member_at_param, family_at_param, line_file.clone()).into()],
            line_file.clone(),
        )?
        .into(),
    ))
}

// Names the pointwise selection condition used by general Cartesian products.
// Example: `$is_choice_function_for(I, S, g, f)` means
// `forall alpha I: f(alpha) $in g(alpha)`.
pub(crate) fn choice_function_for_fact(
    index_set: Obj,
    family_set: Obj,
    family_fn: Obj,
    member: Obj,
    line_file: LineFile,
) -> AtomicFact {
    NormalAtomicFact::new(
        AtomicName::WithoutMod(crate::common::keywords::IS_CHOICE_FUNCTION_FOR.to_string()),
        vec![index_set, family_set, family_fn, member],
        line_file,
    )
    .into()
}

pub(crate) fn general_cart_member_choice_fact(
    general_cart: &GeneralCart,
    member: Obj,
    line_file: LineFile,
) -> AtomicFact {
    choice_function_for_fact(
        general_cart.index_set.as_ref().clone(),
        general_cart.family_set.as_ref().clone(),
        general_cart.family_fn.as_ref().clone(),
        member,
        line_file,
    )
}

pub(crate) fn choice_function_for_definition_facts(
    runtime: &Runtime,
    normal_fact: &NormalAtomicFact,
) -> Result<Option<Vec<Fact>>, RuntimeError> {
    let Some((index_set, family_set, family_fn, member)) = choice_function_for_parts(normal_fact)
    else {
        return Ok(None);
    };
    let general_cart = GeneralCart::new(index_set, family_set, family_fn);
    Ok(
        general_cart_member_pointwise_fact(
            runtime,
            &general_cart,
            &member,
            &normal_fact.line_file,
        )?
        .map(|fact| vec![fact]),
    )
}

pub(crate) fn verify_choice_function_for_arg_types(
    runtime: &mut Runtime,
    atomic_fact: &AtomicFact,
    verify_state: &UseContextVerifyState,
) -> Result<bool, RuntimeError> {
    let (predicate, args, line_file) = match atomic_fact {
        AtomicFact::NormalAtomicFact(fact) => (&fact.predicate, &fact.body, &fact.line_file),
        AtomicFact::NotNormalAtomicFact(fact) => (&fact.predicate, &fact.body, &fact.line_file),
        _ => return Ok(false),
    };
    if !matches!(predicate, AtomicName::WithoutMod(name) if name == crate::common::keywords::IS_CHOICE_FUNCTION_FOR)
    {
        return Ok(false);
    }
    let [index_set, family_set, family_fn, member] = args.as_slice() else {
        return Ok(true);
    };

    let family_param_name = runtime.generate_internal_binder_name();
    let family_fn_set: Obj = FnSet::new(
        vec![runtime.fresh_param_group_with_set(vec![family_param_name], index_set.clone())?],
        vec![],
        family_set.clone(),
    )?
    .into();
    let member_param_name = runtime.generate_internal_binder_name();
    let member_fn_set: Obj = FnSet::new(
        vec![runtime.fresh_param_group_with_set(vec![member_param_name], index_set.clone())?],
        vec![],
        BigUnion::new(family_set.clone()).into(),
    )?
    .into();
    let requirements: Vec<AtomicFact> = vec![
        IsSetFact::new(index_set.clone(), line_file.clone()).into(),
        IsSetFact::new(family_set.clone(), line_file.clone()).into(),
        InFact::new(family_fn.clone(), family_fn_set, line_file.clone()).into(),
        InFact::new(member.clone(), member_fn_set, line_file.clone()).into(),
    ];
    for requirement in requirements {
        if runtime
            .verify_atomic_fact(&requirement, verify_state)?
            .is_unknown()
        {
            return Err(WellDefinedRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    format!(
                        "{} requires I and S to be sets, g in fn(alpha I)S, and f in fn(alpha I)big_union(S)",
                        atomic_fact
                    ),
                    line_file.clone(),
                ),
            )
            .into());
        }
    }
    Ok(true)
}

fn choice_function_for_parts(normal_fact: &NormalAtomicFact) -> Option<(Obj, Obj, Obj, Obj)> {
    if !matches!(&normal_fact.predicate, AtomicName::WithoutMod(name) if name == crate::common::keywords::IS_CHOICE_FUNCTION_FOR)
    {
        return None;
    }
    let [index_set, family_set, family_fn, member] = normal_fact.body.as_slice() else {
        return None;
    };
    Some((
        index_set.clone(),
        family_set.clone(),
        family_fn.clone(),
        member.clone(),
    ))
}
