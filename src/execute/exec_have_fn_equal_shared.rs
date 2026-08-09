use crate::prelude::*;
use std::collections::HashMap;

/// Turn a [`FnSet`] (parser-level function-space type) into a [`FnSetClause`]-shaped bundle.
pub(crate) fn fn_set_to_fn_set_clause(fs: &FnSet) -> FnSetClause {
    FnSetClause::new(
        fs.body.params_def_with_set.clone(),
        fs.body.dom_facts.clone(),
        (*fs.body.ret_set).clone(),
    )
    .expect("fn set signature was already validated")
}

/// Forall parameters, `dom` [`Fact`]s, and curried `(...)(...)` argument layers (one vec per paren
/// group), matching [`HaveFnEqualStmt`]'s `forall` for that signature.
pub(crate) fn forall_binders_dom_and_curried_layers_from_fn_set_clause(
    runtime: &Runtime,
    clause: &FnSetClause,
) -> Result<(ParamDefWithType, Vec<Fact>, Vec<Vec<SymbolBinding>>), RuntimeError> {
    let mut type_groups: Vec<ParamGroupWithParamType> = Vec::new();
    let mut dom_facts: Vec<Fact> = Vec::new();
    let mut layers: Vec<Vec<SymbolBinding>> = Vec::new();
    let mut fn_set_param_to_forall_param: HashMap<String, Obj> = HashMap::new();

    let first_layer_names = append_fn_set_param_groups_as_forall_param_type_groups(
        runtime,
        &clause.params_def_with_set,
        &mut fn_set_param_to_forall_param,
        &mut type_groups,
    )?;
    for d in clause.dom_facts.iter() {
        dom_facts.push(
            runtime
                .inst_or_and_chain_atomic_fact(
                    d,
                    &fn_set_param_to_forall_param,
                    ParamObjType::BinderRetag(BinderRetagSource::FnSet),
                    None,
                )?
                .into(),
        );
    }
    layers.push(first_layer_names);

    let mut ret_set = clause.ret_set.clone();
    while let Obj::FnSet(inner) = ret_set {
        let layer_names = append_fn_set_param_groups_as_forall_param_type_groups(
            runtime,
            &inner.body.params_def_with_set,
            &mut fn_set_param_to_forall_param,
            &mut type_groups,
        )?;

        for d in inner.body.dom_facts.iter() {
            dom_facts.push(
                runtime
                    .inst_or_and_chain_atomic_fact(
                        d,
                        &fn_set_param_to_forall_param,
                        ParamObjType::BinderRetag(BinderRetagSource::FnSet),
                        None,
                    )?
                    .into(),
            );
        }

        layers.push(layer_names);

        ret_set = runtime.inst_obj(
            inner.body.ret_set.as_ref(),
            &fn_set_param_to_forall_param,
            ParamObjType::BinderRetag(BinderRetagSource::FnSet),
        )?;
    }

    Ok((ParamDefWithType::new(type_groups), dom_facts, layers))
}

pub(crate) fn build_curried_function_obj_from_layers_with_binding(
    function: Identifier,
    layer_param_names: &[Vec<SymbolBinding>],
    binding_kind: ParamObjType,
) -> Obj {
    let mut body_vectors: Vec<Vec<Box<Obj>>> = Vec::with_capacity(layer_param_names.len());
    for layer in layer_param_names {
        let mut group: Vec<Box<Obj>> = Vec::with_capacity(layer.len());
        for binding in layer {
            group.push(Box::new(obj_for_bound_param_in_scope(
                binding,
                binding_kind,
            )));
        }
        body_vectors.push(group);
    }
    FnObj::new(FnObjHead::Identifier(function), body_vectors).into()
}

/// Anonymous function value with curried `forall` binders.
pub(crate) fn build_curried_anonymous_fn_from_layers_forall(
    af: &AnonymousFn,
    layer_param_names: &[Vec<SymbolBinding>],
) -> Obj {
    let mut body_vectors: Vec<Vec<Box<Obj>>> = Vec::with_capacity(layer_param_names.len());
    for layer in layer_param_names {
        let mut group: Vec<Box<Obj>> = Vec::with_capacity(layer.len());
        for binding in layer {
            group.push(Box::new(obj_for_bound_param_in_scope(
                binding,
                ParamObjType::Forall,
            )));
        }
        body_vectors.push(group);
    }
    FnObj::new(
        FnObjHead::AnonymousFnLiteral(Box::new(af.clone())),
        body_vectors,
    )
    .into()
}

/// Build `func` applied along `layers` using forall binders; `func` is a name, anonymous fn, or
/// other shape accepted by [`FnObjHead::given_an_atom_return_a_fn_obj_head`].
pub(crate) fn build_curried_fn_value_apply_for_fn_eq(
    func: &Obj,
    layer_param_names: &[Vec<SymbolBinding>],
) -> Option<Obj> {
    // Inside `verify_forall` with `define_params(..., Forall)`, curried args must be
    // `ForallFreeParamObj` so `f(x)` matches the same `x` as user `forall` facts (e.g. chains like
    // `f(x) = x = g(x)`). Function-body binders would not unify with those citations.
    if let Some(identifier) = match func {
        Obj::Atom(AtomObj::Identifier(identifier)) => Some(identifier.clone()),
        _ => None,
    } {
        return Some(build_curried_function_obj_from_layers_with_binding(
            identifier,
            layer_param_names,
            ParamObjType::Forall,
        ));
    }
    if let Obj::AnonymousFn(af) = func {
        return Some(build_curried_anonymous_fn_from_layers_forall(
            af,
            layer_param_names,
        ));
    }
    if let Obj::FnObj(fn_obj) = func {
        let mut applied = fn_obj.clone();
        for layer in layer_param_names {
            let mut args: Vec<Box<Obj>> = Vec::with_capacity(layer.len());
            for binding in layer {
                args.push(Box::new(obj_for_bound_param_in_scope(
                    binding,
                    ParamObjType::Forall,
                )));
            }
            applied.body.push(args);
        }
        return Some(applied.into());
    }
    if let Some(head) = FnObjHead::given_an_atom_return_a_fn_obj_head(func.clone()) {
        let mut body_vectors: Vec<Vec<Box<Obj>>> = Vec::with_capacity(layer_param_names.len());
        for layer in layer_param_names {
            let mut group: Vec<Box<Obj>> = Vec::with_capacity(layer.len());
            for binding in layer {
                group.push(Box::new(obj_for_bound_param_in_scope(
                    binding,
                    ParamObjType::Forall,
                )));
            }
            body_vectors.push(group);
        }
        return Some(FnObj::new(head, body_vectors).into());
    }
    None
}

pub(crate) fn build_declared_function_obj_with_param_bindings(
    function_identifier_obj: Obj,
    param_bindings: &[SymbolBinding],
) -> Obj {
    let function_head = FnObjHead::given_an_atom_return_a_fn_obj_head(function_identifier_obj)
        .expect("declared function identifier should be an atom");
    let params = param_bindings
        .iter()
        .map(|binding| Box::new(obj_for_bound_param_in_scope(binding, ParamObjType::FnSet)))
        .collect();
    FnObj::new(function_head, vec![params]).into()
}

pub(crate) fn forall_param_defs_dom_and_map_from_have_fn_clause(
    runtime: &Runtime,
    clause: &FnSetClause,
) -> Result<(ParamDefWithType, Vec<Fact>, HashMap<String, Obj>), RuntimeError> {
    let mut groups: Vec<ParamGroupWithParamType> =
        Vec::with_capacity(clause.params_def_with_set.len());
    let mut fn_set_param_to_forall_param: HashMap<String, Obj> = HashMap::new();
    append_fn_set_param_groups_as_forall_param_type_groups(
        runtime,
        &clause.params_def_with_set,
        &mut fn_set_param_to_forall_param,
        &mut groups,
    )?;

    let mut dom_facts = Vec::with_capacity(clause.dom_facts.len());
    for dom_fact in clause.dom_facts.iter() {
        dom_facts.push(
            runtime
                .inst_or_and_chain_atomic_fact(
                    dom_fact,
                    &fn_set_param_to_forall_param,
                    ParamObjType::BinderRetag(BinderRetagSource::FnSet),
                    None,
                )?
                .into(),
        );
    }

    Ok((
        ParamDefWithType::new(groups),
        dom_facts,
        fn_set_param_to_forall_param,
    ))
}

fn append_fn_set_param_groups_as_forall_param_type_groups(
    runtime: &Runtime,
    params_def_with_set: &ParamDefWithSet,
    fn_set_param_to_forall_param: &mut HashMap<String, Obj>,
    groups: &mut Vec<ParamGroupWithParamType>,
) -> Result<Vec<SymbolBinding>, RuntimeError> {
    let mut forall_names = Vec::new();
    for param_def_with_set in params_def_with_set.iter() {
        let param_set = runtime.inst_obj(
            param_def_with_set.set_obj(),
            fn_set_param_to_forall_param,
            ParamObjType::BinderRetag(BinderRetagSource::FnSet),
        )?;
        let (group_forall_names, group_map) = runtime
            .fresh_binder_retag_plan_for_bindings(&param_def_with_set.params, ParamObjType::Forall);
        groups.push(ParamGroupWithParamType::new(
            group_forall_names.clone(),
            ParamType::Obj(param_set),
        ));
        for param_binding in param_def_with_set.params.iter() {
            let param_name = param_binding.name();
            insert_symbol_substitution(
                fn_set_param_to_forall_param,
                param_binding,
                group_map[param_name].clone(),
            );
        }
        forall_names.extend(group_forall_names);
    }
    Ok(forall_names)
}

pub(crate) fn case_conditions_are_disjoint(
    runtime: &mut Runtime,
    left: &AndChainAtomicFact,
    right: &AndChainAtomicFact,
) -> Result<bool, RuntimeError> {
    if case_condition_implies_not_other(runtime, left, right)? {
        return Ok(true);
    }
    case_condition_implies_not_other(runtime, right, left)
}

fn case_condition_implies_not_other(
    runtime: &mut Runtime,
    assumed: &AndChainAtomicFact,
    other: &AndChainAtomicFact,
) -> Result<bool, RuntimeError> {
    runtime.run_in_local_env(|rt| {
        rt.store_with_well_defined_verification_and_infer_with_default_verify_state(Fact::from(
            assumed.clone(),
        ))?;

        for atom in flatten_and_chain_to_atomic_facts(other) {
            let Ok(negated) = atom.logical_negation() else {
                continue;
            };
            let result = rt.verify_atomic_fact(&negated, &UseContextVerifyState::new(0, false))?;
            if result.is_true() {
                return Ok(true);
            }
        }
        Ok(false)
    })
}

fn flatten_and_chain_to_atomic_facts(fact: &AndChainAtomicFact) -> Vec<AtomicFact> {
    match fact {
        AndChainAtomicFact::AtomicFact(atomic_fact) => vec![atomic_fact.clone()],
        AndChainAtomicFact::AndFact(and_fact) => and_fact.facts.clone(),
        AndChainAtomicFact::ChainFact(chain_fact) => chain_fact.facts().unwrap(),
    }
}

impl Runtime {
    // Parser and executor must use the same object form for declarations in a
    // named module. Example: `have fn f ...` in `m` stores facts about `m::f`.
    pub(crate) fn declared_identifier_obj(&self, name: &str) -> Obj {
        let symbol = self
            .visible_symbol_definition(name)
            .map(|definition| definition.binding().as_ref());
        if let Some(module_name) = self.current_parse_namespace() {
            return match symbol {
                Some(symbol) => {
                    IdentifierWithMod::new_bound(module_name.to_string(), name.to_string(), symbol)
                        .into()
                }
                None => IdentifierWithMod::new(module_name.to_string(), name.to_string()).into(),
            };
        }
        match symbol {
            Some(symbol) => Identifier::new_bound(name.to_string(), symbol).into(),
            None => Identifier::new(name.to_string()).into(),
        }
    }
}
