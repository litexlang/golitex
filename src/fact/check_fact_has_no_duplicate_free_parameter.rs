use crate::prelude::*;

pub fn check_forall_fact_has_no_duplicate_forall_free_parameter(
    forall_fact: &ForallFact,
) -> Result<(), RuntimeError> {
    let mut params_already_used: Vec<Vec<String>> = Vec::new();
    check_forall_fact_has_no_duplicate_free_parameter(
        forall_fact,
        ParamObjType::Forall,
        &mut params_already_used,
    )
}

pub fn check_exist_fact_has_no_duplicate_exist_free_parameter(
    exist_fact: &ExistFactEnum,
) -> Result<(), RuntimeError> {
    let mut params_already_used: Vec<Vec<String>> = Vec::new();
    check_exist_fact_has_no_duplicate_free_parameter(
        exist_fact,
        ParamObjType::Exist,
        &mut params_already_used,
    )
}

pub fn check_forall_fact_with_iff_has_no_duplicate_forall_free_parameter(
    forall_fact_with_iff: &ForallFactWithIff,
) -> Result<(), RuntimeError> {
    let mut params_already_used: Vec<Vec<String>> = Vec::new();
    check_forall_fact_with_iff_has_no_duplicate_free_parameter(
        forall_fact_with_iff,
        ParamObjType::Forall,
        &mut params_already_used,
    )
}

fn check_fact_has_no_duplicate_free_parameter(
    fact: &Fact,
    free_param_type: ParamObjType,
    params_already_used: &mut Vec<Vec<String>>,
) -> Result<(), RuntimeError> {
    match fact {
        Fact::AtomicFact(_) => Ok(()),
        Fact::ExistFact(exist_fact) => check_exist_fact_has_no_duplicate_free_parameter(
            exist_fact,
            free_param_type,
            params_already_used,
        ),
        Fact::OrFact(or_fact) => check_or_fact_has_no_duplicate_free_parameter(
            or_fact,
            free_param_type,
            params_already_used,
        ),
        Fact::AndFact(_) => Ok(()),
        Fact::ChainFact(_) => Ok(()),
        Fact::ForallFact(forall_fact) => check_forall_fact_has_no_duplicate_free_parameter(
            forall_fact,
            free_param_type,
            params_already_used,
        ),
        Fact::ForallFactWithIff(forall_fact_with_iff) => {
            check_forall_fact_with_iff_has_no_duplicate_free_parameter(
                forall_fact_with_iff,
                free_param_type,
                params_already_used,
            )
        }
        Fact::NotForall(not_forall) => check_forall_fact_has_no_duplicate_free_parameter(
            &not_forall.forall_fact,
            free_param_type,
            params_already_used,
        ),
    }
}

fn check_forall_fact_with_iff_has_no_duplicate_free_parameter(
    forall_fact_with_iff: &ForallFactWithIff,
    free_param_type: ParamObjType,
    params_already_used: &mut Vec<Vec<String>>,
) -> Result<(), RuntimeError> {
    let pushed_scope = push_forall_scope_if_needed(
        &forall_fact_with_iff.forall_fact,
        free_param_type,
        params_already_used,
    )?;

    for fact in forall_fact_with_iff.forall_fact.dom_facts.iter() {
        check_fact_has_no_duplicate_free_parameter(fact, free_param_type, params_already_used)?;
    }

    for fact in forall_fact_with_iff.forall_fact.then_facts.iter() {
        check_exist_or_and_chain_atomic_fact_has_no_duplicate_free_parameter(
            fact,
            free_param_type,
            params_already_used,
        )?;
    }

    for fact in forall_fact_with_iff.iff_facts.iter() {
        check_exist_or_and_chain_atomic_fact_has_no_duplicate_free_parameter(
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

fn check_forall_fact_has_no_duplicate_free_parameter(
    forall_fact: &ForallFact,
    free_param_type: ParamObjType,
    params_already_used: &mut Vec<Vec<String>>,
) -> Result<(), RuntimeError> {
    let pushed_scope =
        push_forall_scope_if_needed(forall_fact, free_param_type, params_already_used)?;

    for fact in forall_fact.dom_facts.iter() {
        check_fact_has_no_duplicate_free_parameter(fact, free_param_type, params_already_used)?;
    }

    for fact in forall_fact.then_facts.iter() {
        check_exist_or_and_chain_atomic_fact_has_no_duplicate_free_parameter(
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

fn push_forall_scope_if_needed(
    forall_fact: &ForallFact,
    free_param_type: ParamObjType,
    params_already_used: &mut Vec<Vec<String>>,
) -> Result<bool, RuntimeError> {
    if free_param_type != ParamObjType::Forall {
        return Ok(false);
    }

    push_param_def_scope_or_error(
        forall_fact.params_def_with_type.collect_param_names(),
        free_param_type,
        &forall_fact.line_file,
        params_already_used,
    )?;
    Ok(true)
}

fn check_exist_fact_has_no_duplicate_free_parameter(
    exist_fact: &ExistFactEnum,
    free_param_type: ParamObjType,
    params_already_used: &mut Vec<Vec<String>>,
) -> Result<(), RuntimeError> {
    let pushed_scope =
        push_exist_scope_if_needed(exist_fact, free_param_type, params_already_used)?;

    for fact in exist_fact.facts().iter() {
        check_exist_body_fact_has_no_duplicate_free_parameter(
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

pub fn check_exist_body_fact_has_no_duplicate_free_parameter(
    fact: &ExistBodyFact,
    free_param_type: ParamObjType,
    params_already_used: &mut Vec<Vec<String>>,
) -> Result<(), RuntimeError> {
    match fact {
        ExistBodyFact::AtomicFact(_) => Ok(()),
        ExistBodyFact::AndFact(_) => Ok(()),
        ExistBodyFact::ChainFact(_) => Ok(()),
        ExistBodyFact::OrFact(or_fact) => check_or_fact_has_no_duplicate_free_parameter(
            or_fact,
            free_param_type,
            params_already_used,
        ),
        ExistBodyFact::InlineForall(forall_fact) => {
            check_forall_fact_has_no_duplicate_free_parameter(
                forall_fact,
                free_param_type,
                params_already_used,
            )
        }
    }
}

fn push_exist_scope_if_needed(
    exist_fact: &ExistFactEnum,
    free_param_type: ParamObjType,
    params_already_used: &mut Vec<Vec<String>>,
) -> Result<bool, RuntimeError> {
    if free_param_type != ParamObjType::Exist {
        return Ok(false);
    }

    let body = exist_fact.body();
    push_param_def_scope_or_error(
        body.params_def_with_type.collect_param_names(),
        free_param_type,
        &body.line_file,
        params_already_used,
    )?;
    Ok(true)
}

fn check_exist_or_and_chain_atomic_fact_has_no_duplicate_free_parameter(
    fact: &ExistOrAndChainAtomicFact,
    free_param_type: ParamObjType,
    params_already_used: &mut Vec<Vec<String>>,
) -> Result<(), RuntimeError> {
    match fact {
        ExistOrAndChainAtomicFact::AtomicFact(_) => Ok(()),
        ExistOrAndChainAtomicFact::AndFact(_) => Ok(()),
        ExistOrAndChainAtomicFact::ChainFact(_) => Ok(()),
        ExistOrAndChainAtomicFact::OrFact(or_fact) => {
            check_or_fact_has_no_duplicate_free_parameter(
                or_fact,
                free_param_type,
                params_already_used,
            )
        }
        ExistOrAndChainAtomicFact::ExistFact(exist_fact) => {
            check_exist_fact_has_no_duplicate_free_parameter(
                exist_fact,
                free_param_type,
                params_already_used,
            )
        }
    }
}

fn check_or_fact_has_no_duplicate_free_parameter(
    or_fact: &OrFact,
    free_param_type: ParamObjType,
    params_already_used: &mut Vec<Vec<String>>,
) -> Result<(), RuntimeError> {
    for fact in or_fact.facts.iter() {
        check_and_chain_atomic_fact_has_no_duplicate_free_parameter(
            fact,
            free_param_type,
            params_already_used,
        )?;
    }
    Ok(())
}

fn check_and_chain_atomic_fact_has_no_duplicate_free_parameter(
    fact: &AndChainAtomicFact,
    _free_param_type: ParamObjType,
    _params_already_used: &mut Vec<Vec<String>>,
) -> Result<(), RuntimeError> {
    match fact {
        AndChainAtomicFact::AtomicFact(_) => Ok(()),
        AndChainAtomicFact::AndFact(_) => Ok(()),
        AndChainAtomicFact::ChainFact(_) => Ok(()),
    }
}

fn push_param_def_scope_or_error(
    param_names: Vec<String>,
    free_param_type: ParamObjType,
    line_file: &LineFile,
    params_already_used: &mut Vec<Vec<String>>,
) -> Result<(), RuntimeError> {
    let mut params_in_current_scope: Vec<String> = Vec::new();
    for param_name in param_names.iter() {
        if params_in_current_scope.contains(param_name) {
            return Err(duplicate_param_error(
                param_name,
                free_param_type,
                line_file.clone(),
            ));
        }

        if param_name_already_used(param_name, params_already_used) {
            return Err(duplicate_param_error(
                param_name,
                free_param_type,
                line_file.clone(),
            ));
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

fn duplicate_param_error(
    param_name: &String,
    free_param_type: ParamObjType,
    line_file: LineFile,
) -> RuntimeError {
    DefineParamsRuntimeError(RuntimeErrorStruct::new_with_msg_and_line_file(
        format!(
            "duplicate {:?} free parameter `{}` in nested scope",
            free_param_type, param_name
        ),
        line_file,
    ))
    .into()
}
