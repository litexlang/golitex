use crate::prelude::*;
use std::collections::HashMap;

/// Turn a [`FnSet`] (parser-level function-space type) into a [`FnSetClause`]-shaped bundle.
pub fn fn_set_to_fn_set_clause(fs: &FnSet) -> FnSetClause {
    FnSetClause::new(
        fs.body.set_bound_parameters.clone(),
        fs.body.dom_facts.clone(),
        (*fs.body.ret_set).clone(),
    )
    .expect("fn set signature was already validated")
}

/// Forall parameters, `dom` [`Fact`]s, and curried `(...)(...)` argument layers (one vec per paren
/// group), matching [`HaveFnEqualStmt`]'s `forall` for that signature.
pub fn forall_binders_dom_and_curried_layers_from_fn_set_clause(
    runtime: &Runtime,
    clause: &FnSetClause,
) -> Result<(TypedParameterList, Vec<Fact>, Vec<Vec<SymbolBinding>>), RuntimeError> {
    let mut type_groups: Vec<TypedParameterGroup> = Vec::new();
    let mut dom_facts: Vec<Fact> = Vec::new();
    let mut layers: Vec<Vec<SymbolBinding>> = Vec::new();
    let mut fn_set_param_to_forall_param: HashMap<String, Obj> = HashMap::new();

    let first_layer_names = append_fn_set_param_groups_as_forall_param_type_groups(
        runtime,
        &clause.set_bound_parameters,
        &mut fn_set_param_to_forall_param,
        &mut type_groups,
    )?;
    for d in clause.dom_facts.iter() {
        dom_facts.push(
            runtime
                .inst_quantifier_free_fact(
                    d,
                    &fn_set_param_to_forall_param,
                    SubstitutionMode::Exact,
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
            &inner.body.set_bound_parameters,
            &mut fn_set_param_to_forall_param,
            &mut type_groups,
        )?;

        for d in inner.body.dom_facts.iter() {
            dom_facts.push(
                runtime
                    .inst_quantifier_free_fact(
                        d,
                        &fn_set_param_to_forall_param,
                        SubstitutionMode::Exact,
                        None,
                    )?
                    .into(),
            );
        }

        layers.push(layer_names);

        ret_set = runtime.inst_obj(
            inner.body.ret_set.as_ref(),
            &fn_set_param_to_forall_param,
            SubstitutionMode::Exact,
        )?;
    }

    Ok((TypedParameterList::new(type_groups), dom_facts, layers))
}

pub fn build_curried_function_obj_from_layers_with_binding(
    function: Identifier,
    layer_param_names: &[Vec<SymbolBinding>],
) -> Obj {
    let mut body_vectors: Vec<Vec<Box<Obj>>> = Vec::with_capacity(layer_param_names.len());
    for layer in layer_param_names {
        let mut group: Vec<Box<Obj>> = Vec::with_capacity(layer.len());
        for binding in layer {
            group.push(Box::new(obj_for_bound_param_in_scope(binding)));
        }
        body_vectors.push(group);
    }
    FnObj::new(FnObjHead::Identifier(function), body_vectors).into()
}

/// Anonymous function value with curried `forall` binders.
pub fn build_curried_anonymous_fn_from_layers_forall(
    af: &AnonymousFn,
    layer_param_names: &[Vec<SymbolBinding>],
) -> Obj {
    let mut body_vectors: Vec<Vec<Box<Obj>>> = Vec::with_capacity(layer_param_names.len());
    for layer in layer_param_names {
        let mut group: Vec<Box<Obj>> = Vec::with_capacity(layer.len());
        for binding in layer {
            group.push(Box::new(obj_for_bound_param_in_scope(binding)));
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
pub fn build_curried_fn_value_apply_for_fn_eq(
    func: &Obj,
    layer_param_names: &[Vec<SymbolBinding>],
) -> Option<Obj> {
    // Curried arguments retain the exact bindings allocated by the surrounding forall.
    if let Some(identifier) = match func {
        Obj::Atom(AtomObj::Identifier(identifier)) => Some(identifier.clone()),
        _ => None,
    } {
        return Some(build_curried_function_obj_from_layers_with_binding(
            identifier,
            layer_param_names,
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
                args.push(Box::new(obj_for_bound_param_in_scope(binding)));
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
                group.push(Box::new(obj_for_bound_param_in_scope(binding)));
            }
            body_vectors.push(group);
        }
        return Some(FnObj::new(head, body_vectors).into());
    }
    None
}

pub fn build_defined_function_obj_with_parameter_bindings(
    function_identifier_obj: Obj,
    param_bindings: &[SymbolBinding],
) -> Obj {
    let function_head = FnObjHead::given_an_atom_return_a_fn_obj_head(function_identifier_obj)
        .expect("defined function identifier should be an atom");
    let params = param_bindings
        .iter()
        .map(|binding| Box::new(obj_for_bound_param_in_scope(binding)))
        .collect();
    FnObj::new(function_head, vec![params]).into()
}

pub fn forall_param_defs_dom_and_map_from_have_fn_clause(
    runtime: &Runtime,
    clause: &FnSetClause,
) -> Result<(TypedParameterList, Vec<Fact>, HashMap<String, Obj>), RuntimeError> {
    let mut groups: Vec<TypedParameterGroup> =
        Vec::with_capacity(clause.set_bound_parameters.len());
    let mut fn_set_param_to_forall_param: HashMap<String, Obj> = HashMap::new();
    append_fn_set_param_groups_as_forall_param_type_groups(
        runtime,
        &clause.set_bound_parameters,
        &mut fn_set_param_to_forall_param,
        &mut groups,
    )?;

    let mut dom_facts = Vec::with_capacity(clause.dom_facts.len());
    for dom_fact in clause.dom_facts.iter() {
        dom_facts.push(
            runtime
                .inst_quantifier_free_fact(
                    dom_fact,
                    &fn_set_param_to_forall_param,
                    SubstitutionMode::Exact,
                    None,
                )?
                .into(),
        );
    }

    Ok((
        TypedParameterList::new(groups),
        dom_facts,
        fn_set_param_to_forall_param,
    ))
}

fn append_fn_set_param_groups_as_forall_param_type_groups(
    runtime: &Runtime,
    set_bound_parameters: &SetBoundParameterList,
    fn_set_param_to_forall_param: &mut HashMap<String, Obj>,
    groups: &mut Vec<TypedParameterGroup>,
) -> Result<Vec<SymbolBinding>, RuntimeError> {
    let mut forall_names = Vec::new();
    for param_def_with_set in set_bound_parameters.iter() {
        let param_set = runtime.inst_obj(
            param_def_with_set.set_obj(),
            fn_set_param_to_forall_param,
            SubstitutionMode::Exact,
        )?;
        let (group_forall_names, group_map) =
            runtime.fresh_binder_retag_plan_for_bindings(&param_def_with_set.params);
        groups.push(TypedParameterGroup::new(
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

pub fn case_conditions_are_disjoint(
    runtime: &mut Runtime,
    left: &AndChainAtomicFact,
    right: &AndChainAtomicFact,
) -> Result<bool, RuntimeError> {
    Ok(case_conditions_are_disjoint_result(runtime, 0, 1, left, right)?.is_some())
}

pub fn case_conditions_are_disjoint_result(
    runtime: &mut Runtime,
    left_case_index: usize,
    right_case_index: usize,
    left: &AndChainAtomicFact,
    right: &AndChainAtomicFact,
) -> Result<Option<SuccessVerifyCaseDisjointnessResult>, RuntimeError> {
    if let Some(result) = case_condition_implies_not_other_result(
        runtime,
        left_case_index,
        right_case_index,
        CaseDisjointnessOrientation::LeftImpliesNotRight,
        left,
        right,
    )? {
        return Ok(Some(result));
    }
    case_condition_implies_not_other_result(
        runtime,
        left_case_index,
        right_case_index,
        CaseDisjointnessOrientation::RightImpliesNotLeft,
        right,
        left,
    )
}

fn case_condition_implies_not_other_result(
    runtime: &mut Runtime,
    left_case_index: usize,
    right_case_index: usize,
    orientation: CaseDisjointnessOrientation,
    assumed: &AndChainAtomicFact,
    other: &AndChainAtomicFact,
) -> Result<Option<SuccessVerifyCaseDisjointnessResult>, RuntimeError> {
    runtime.run_in_local_env(|rt| {
        let assumed_case = Fact::from(assumed.clone());
        let mut infers = rt
            .store_with_well_defined_verification_and_infer_with_default_verify_state(
                assumed_case.clone(),
            )?;
        rt.attach_known_fact_ids_to_infer_result(&mut infers)?;
        let fact_id = rt.known_fact_id_for_fact(&assumed_case)?;
        let assumption_store = SuccessStoreFactResult {
            fact: assumed_case.clone(),
            fact_id,
            infers,
        };

        for atom in flatten_and_chain_to_atomic_facts(rt, other) {
            let Ok(negated) = atom.logical_negation_with_runtime(rt) else {
                continue;
            };
            let mut result = rt.verify_atomic_fact(&negated, &VerifyState::initial())?;
            if result.is_success() {
                rt.attach_known_fact_ids_to_verify_fact_result(&mut result)?;
                return Ok(Some(SuccessVerifyCaseDisjointnessResult {
                    left_case_index,
                    right_case_index,
                    orientation,
                    assumed_case,
                    assumption_store,
                    contradicted_atom: atom,
                    negated_atom: negated,
                    negated_atom_check: Box::new(result),
                }));
            }
        }
        Ok(None)
    })
}

fn flatten_and_chain_to_atomic_facts(
    runtime: &Runtime,
    fact: &AndChainAtomicFact,
) -> Vec<AtomicFact> {
    match fact {
        AndChainAtomicFact::AtomicFact(atomic_fact) => vec![atomic_fact.clone()],
        AndChainAtomicFact::AndFact(and_fact) => and_fact.facts.clone(),
        AndChainAtomicFact::ChainFact(chain_fact) => chain_fact.facts(runtime).unwrap(),
    }
}

impl Runtime {
    // Parser and executor must use the same object form for definitions in a
    // named module. Example: `have fn f ...` in `m` stores facts about `m::f`.
    pub fn definition_identifier_obj(&self, name: &str) -> Obj {
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
