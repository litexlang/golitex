use crate::prelude::*;

pub fn check_set_builder_has_no_duplicate_set_builder_free_parameter(
    set_builder: &SetBuilder,
) -> Result<(), RuntimeError> {
    let mut params_already_used: Vec<Vec<String>> = Vec::new();
    check_set_builder_has_no_duplicate_free_parameter(
        set_builder,
        ParamObjType::SetBuilder,
        &mut params_already_used,
    )
}

pub fn check_fn_set_has_no_duplicate_fn_set_free_parameter(
    fn_set: &FnSet,
) -> Result<(), RuntimeError> {
    let mut params_already_used: Vec<Vec<String>> = Vec::new();
    check_fn_set_body_has_no_duplicate_free_parameter(
        &fn_set.body,
        ParamObjType::FnSet,
        &mut params_already_used,
    )
}

pub fn check_anonymous_fn_has_no_duplicate_fn_set_free_parameter(
    anonymous_fn: &AnonymousFn,
) -> Result<(), RuntimeError> {
    let mut params_already_used: Vec<Vec<String>> = Vec::new();
    check_anonymous_fn_has_no_duplicate_free_parameter(
        anonymous_fn,
        ParamObjType::FnSet,
        &mut params_already_used,
    )
}

fn check_obj_has_no_duplicate_free_parameter(
    obj: &Obj,
    free_param_type: ParamObjType,
    params_already_used: &mut Vec<Vec<String>>,
) -> Result<(), RuntimeError> {
    match obj {
        Obj::Atom(_) | Obj::Number(_) | Obj::StandardSet(_) => Ok(()),
        Obj::FnObj(fn_obj) => {
            for group in fn_obj.body.iter() {
                for obj in group.iter() {
                    check_obj_has_no_duplicate_free_parameter(
                        obj,
                        free_param_type,
                        params_already_used,
                    )?;
                }
            }
            Ok(())
        }
        Obj::Add(obj) => {
            check_two_objs(&obj.left, &obj.right, free_param_type, params_already_used)
        }
        Obj::Sub(obj) => {
            check_two_objs(&obj.left, &obj.right, free_param_type, params_already_used)
        }
        Obj::Mul(obj) => {
            check_two_objs(&obj.left, &obj.right, free_param_type, params_already_used)
        }
        Obj::Div(obj) => {
            check_two_objs(&obj.left, &obj.right, free_param_type, params_already_used)
        }
        Obj::Mod(obj) => {
            check_two_objs(&obj.left, &obj.right, free_param_type, params_already_used)
        }
        Obj::Pow(obj) => check_two_objs(
            &obj.base,
            &obj.exponent,
            free_param_type,
            params_already_used,
        ),
        Obj::Abs(obj) => check_obj_has_no_duplicate_free_parameter(
            &obj.arg,
            free_param_type,
            params_already_used,
        ),
        Obj::Log(obj) => check_two_objs(&obj.base, &obj.arg, free_param_type, params_already_used),
        Obj::Max(obj) => {
            check_two_objs(&obj.left, &obj.right, free_param_type, params_already_used)
        }
        Obj::Min(obj) => {
            check_two_objs(&obj.left, &obj.right, free_param_type, params_already_used)
        }
        Obj::Union(obj) => {
            check_two_objs(&obj.left, &obj.right, free_param_type, params_already_used)
        }
        Obj::Intersect(obj) => {
            check_two_objs(&obj.left, &obj.right, free_param_type, params_already_used)
        }
        Obj::SetMinus(obj) => {
            check_two_objs(&obj.left, &obj.right, free_param_type, params_already_used)
        }
        Obj::SetDiff(obj) => {
            check_two_objs(&obj.left, &obj.right, free_param_type, params_already_used)
        }
        Obj::Cup(obj) => check_obj_has_no_duplicate_free_parameter(
            &obj.left,
            free_param_type,
            params_already_used,
        ),
        Obj::Cap(obj) => check_obj_has_no_duplicate_free_parameter(
            &obj.left,
            free_param_type,
            params_already_used,
        ),
        Obj::PowerSet(obj) => check_obj_has_no_duplicate_free_parameter(
            &obj.set,
            free_param_type,
            params_already_used,
        ),
        Obj::ListSet(obj) => {
            for item in obj.list.iter() {
                check_obj_has_no_duplicate_free_parameter(
                    item,
                    free_param_type,
                    params_already_used,
                )?;
            }
            Ok(())
        }
        Obj::SetBuilder(set_builder) => check_set_builder_has_no_duplicate_free_parameter(
            set_builder,
            free_param_type,
            params_already_used,
        ),
        Obj::FnSet(fn_set) => check_fn_set_body_has_no_duplicate_free_parameter(
            &fn_set.body,
            free_param_type,
            params_already_used,
        ),
        Obj::AnonymousFn(anonymous_fn) => check_anonymous_fn_has_no_duplicate_free_parameter(
            anonymous_fn,
            free_param_type,
            params_already_used,
        ),
        Obj::Cart(obj) => {
            for arg in obj.args.iter() {
                check_obj_has_no_duplicate_free_parameter(
                    arg,
                    free_param_type,
                    params_already_used,
                )?;
            }
            Ok(())
        }
        Obj::CartDim(obj) => check_obj_has_no_duplicate_free_parameter(
            &obj.set,
            free_param_type,
            params_already_used,
        ),
        Obj::Proj(obj) => check_two_objs(&obj.set, &obj.dim, free_param_type, params_already_used),
        Obj::TupleDim(obj) => check_obj_has_no_duplicate_free_parameter(
            &obj.arg,
            free_param_type,
            params_already_used,
        ),
        Obj::Tuple(obj) => {
            for arg in obj.args.iter() {
                check_obj_has_no_duplicate_free_parameter(
                    arg,
                    free_param_type,
                    params_already_used,
                )?;
            }
            Ok(())
        }
        Obj::Count(obj) => check_obj_has_no_duplicate_free_parameter(
            &obj.set,
            free_param_type,
            params_already_used,
        ),
        Obj::Sum(obj) => {
            check_obj_has_no_duplicate_free_parameter(
                &obj.start,
                free_param_type,
                params_already_used,
            )?;
            check_obj_has_no_duplicate_free_parameter(
                &obj.end,
                free_param_type,
                params_already_used,
            )?;
            check_obj_has_no_duplicate_free_parameter(
                &obj.func,
                free_param_type,
                params_already_used,
            )
        }
        Obj::Product(obj) => {
            check_obj_has_no_duplicate_free_parameter(
                &obj.start,
                free_param_type,
                params_already_used,
            )?;
            check_obj_has_no_duplicate_free_parameter(
                &obj.end,
                free_param_type,
                params_already_used,
            )?;
            check_obj_has_no_duplicate_free_parameter(
                &obj.func,
                free_param_type,
                params_already_used,
            )
        }
        Obj::Range(obj) => {
            check_two_objs(&obj.start, &obj.end, free_param_type, params_already_used)
        }
        Obj::ClosedRange(obj) => {
            check_two_objs(&obj.start, &obj.end, free_param_type, params_already_used)
        }
        Obj::FnRange(obj) => check_obj_has_no_duplicate_free_parameter(
            &obj.fn_obj,
            free_param_type,
            params_already_used,
        ),
        Obj::FnDom(obj) => check_obj_has_no_duplicate_free_parameter(
            &obj.fn_obj,
            free_param_type,
            params_already_used,
        ),
        Obj::FiniteSeqSet(obj) => {
            check_two_objs(&obj.set, &obj.n, free_param_type, params_already_used)
        }
        Obj::SeqSet(obj) => check_obj_has_no_duplicate_free_parameter(
            &obj.set,
            free_param_type,
            params_already_used,
        ),
        Obj::FiniteSeqListObj(obj) => {
            for item in obj.objs.iter() {
                check_obj_has_no_duplicate_free_parameter(
                    item,
                    free_param_type,
                    params_already_used,
                )?;
            }
            Ok(())
        }
        Obj::Choose(obj) => check_obj_has_no_duplicate_free_parameter(
            &obj.set,
            free_param_type,
            params_already_used,
        ),
        Obj::ObjAtIndex(obj) => {
            check_two_objs(&obj.obj, &obj.index, free_param_type, params_already_used)
        }
        Obj::FamilyObj(obj) => {
            for param in obj.params.iter() {
                check_obj_has_no_duplicate_free_parameter(
                    param,
                    free_param_type,
                    params_already_used,
                )?;
            }
            Ok(())
        }
        Obj::StructObj(obj) => {
            for param in obj.params.iter() {
                check_obj_has_no_duplicate_free_parameter(
                    param,
                    free_param_type,
                    params_already_used,
                )?;
            }
            Ok(())
        }
        Obj::ObjAsStructInstanceWithFieldAccess(obj) => {
            for param in obj.struct_obj.params.iter() {
                check_obj_has_no_duplicate_free_parameter(
                    param,
                    free_param_type,
                    params_already_used,
                )?;
            }
            check_obj_has_no_duplicate_free_parameter(
                &obj.obj,
                free_param_type,
                params_already_used,
            )
        }
        Obj::MatrixSet(obj) => {
            check_obj_has_no_duplicate_free_parameter(
                &obj.set,
                free_param_type,
                params_already_used,
            )?;
            check_obj_has_no_duplicate_free_parameter(
                &obj.row_len,
                free_param_type,
                params_already_used,
            )?;
            check_obj_has_no_duplicate_free_parameter(
                &obj.col_len,
                free_param_type,
                params_already_used,
            )
        }
        Obj::MatrixListObj(obj) => {
            for row in obj.rows.iter() {
                for item in row.iter() {
                    check_obj_has_no_duplicate_free_parameter(
                        item,
                        free_param_type,
                        params_already_used,
                    )?;
                }
            }
            Ok(())
        }
        Obj::MatrixAdd(obj) => {
            check_two_objs(&obj.left, &obj.right, free_param_type, params_already_used)
        }
        Obj::MatrixSub(obj) => {
            check_two_objs(&obj.left, &obj.right, free_param_type, params_already_used)
        }
        Obj::MatrixMul(obj) => {
            check_two_objs(&obj.left, &obj.right, free_param_type, params_already_used)
        }
        Obj::MatrixScalarMul(obj) => check_two_objs(
            &obj.scalar,
            &obj.matrix,
            free_param_type,
            params_already_used,
        ),
        Obj::MatrixPow(obj) => check_two_objs(
            &obj.base,
            &obj.exponent,
            free_param_type,
            params_already_used,
        ),
    }
}

fn check_set_builder_has_no_duplicate_free_parameter(
    set_builder: &SetBuilder,
    free_param_type: ParamObjType,
    params_already_used: &mut Vec<Vec<String>>,
) -> Result<(), RuntimeError> {
    let pushed_scope = if free_param_type == ParamObjType::SetBuilder {
        push_param_names_scope_or_error(
            vec![set_builder.param.clone()],
            free_param_type,
            params_already_used,
        )?;
        true
    } else {
        false
    };

    check_obj_has_no_duplicate_free_parameter(
        &set_builder.param_set,
        free_param_type,
        params_already_used,
    )?;

    for fact in set_builder.facts.iter() {
        check_or_and_chain_atomic_fact_has_no_duplicate_free_parameter(
            fact,
            free_param_type,
            params_already_used,
        )?;
    }

    if pushed_scope {
        params_already_used.pop();
    }
    Ok(())
}

fn check_fn_set_body_has_no_duplicate_free_parameter(
    body: &FnSetBody,
    free_param_type: ParamObjType,
    params_already_used: &mut Vec<Vec<String>>,
) -> Result<(), RuntimeError> {
    let pushed_scope = if free_param_type == ParamObjType::FnSet {
        push_param_names_scope_or_error(
            ParamGroupWithSet::collect_param_names(&body.params_def_with_set),
            free_param_type,
            params_already_used,
        )?;
        true
    } else {
        false
    };

    for param_def in body.params_def_with_set.iter() {
        check_obj_has_no_duplicate_free_parameter(
            param_def.set_obj(),
            free_param_type,
            params_already_used,
        )?;
    }

    for fact in body.dom_facts.iter() {
        check_or_and_chain_atomic_fact_has_no_duplicate_free_parameter(
            fact,
            free_param_type,
            params_already_used,
        )?;
    }
    check_obj_has_no_duplicate_free_parameter(&body.ret_set, free_param_type, params_already_used)?;

    if pushed_scope {
        params_already_used.pop();
    }
    Ok(())
}

fn check_anonymous_fn_has_no_duplicate_free_parameter(
    anonymous_fn: &AnonymousFn,
    free_param_type: ParamObjType,
    params_already_used: &mut Vec<Vec<String>>,
) -> Result<(), RuntimeError> {
    let pushed_scope = if free_param_type == ParamObjType::FnSet {
        push_param_names_scope_or_error(
            ParamGroupWithSet::collect_param_names(&anonymous_fn.body.params_def_with_set),
            free_param_type,
            params_already_used,
        )?;
        true
    } else {
        false
    };

    for param_def in anonymous_fn.body.params_def_with_set.iter() {
        check_obj_has_no_duplicate_free_parameter(
            param_def.set_obj(),
            free_param_type,
            params_already_used,
        )?;
    }

    for fact in anonymous_fn.body.dom_facts.iter() {
        check_or_and_chain_atomic_fact_has_no_duplicate_free_parameter(
            fact,
            free_param_type,
            params_already_used,
        )?;
    }
    check_obj_has_no_duplicate_free_parameter(
        &anonymous_fn.body.ret_set,
        free_param_type,
        params_already_used,
    )?;
    check_obj_has_no_duplicate_free_parameter(
        &anonymous_fn.equal_to,
        free_param_type,
        params_already_used,
    )?;

    if pushed_scope {
        params_already_used.pop();
    }
    Ok(())
}

fn check_or_and_chain_atomic_fact_has_no_duplicate_free_parameter(
    fact: &OrAndChainAtomicFact,
    free_param_type: ParamObjType,
    params_already_used: &mut Vec<Vec<String>>,
) -> Result<(), RuntimeError> {
    for obj in fact.get_args_from_fact().iter() {
        check_obj_has_no_duplicate_free_parameter(obj, free_param_type, params_already_used)?;
    }
    Ok(())
}

fn check_two_objs(
    left: &Obj,
    right: &Obj,
    free_param_type: ParamObjType,
    params_already_used: &mut Vec<Vec<String>>,
) -> Result<(), RuntimeError> {
    check_obj_has_no_duplicate_free_parameter(left, free_param_type, params_already_used)?;
    check_obj_has_no_duplicate_free_parameter(right, free_param_type, params_already_used)
}

fn push_param_names_scope_or_error(
    param_names: Vec<String>,
    free_param_type: ParamObjType,
    params_already_used: &mut Vec<Vec<String>>,
) -> Result<(), RuntimeError> {
    let mut params_in_current_scope: Vec<String> = Vec::new();
    for param_name in param_names.iter() {
        if params_in_current_scope.contains(param_name)
            || param_name_already_used(param_name, params_already_used)
        {
            return Err(duplicate_param_error(param_name, free_param_type));
        }
        params_in_current_scope.push(param_name.clone());
    }

    params_already_used.push(params_in_current_scope);
    Ok(())
}

fn param_name_already_used(param_name: &String, params_already_used: &Vec<Vec<String>>) -> bool {
    for params_in_scope in params_already_used.iter() {
        if params_in_scope.contains(param_name) {
            return true;
        }
    }
    false
}

fn duplicate_param_error(param_name: &String, free_param_type: ParamObjType) -> RuntimeError {
    DefineParamsRuntimeError(RuntimeErrorStruct::new_with_msg_and_line_file(
        format!(
            "duplicate {:?} free parameter `{}` in nested object scope",
            free_param_type, param_name
        ),
        default_line_file(),
    ))
    .into()
}
