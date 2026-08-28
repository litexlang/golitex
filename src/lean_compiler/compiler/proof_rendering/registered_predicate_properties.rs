//! Registered reflexive, symmetric, antisymmetric, and transitive predicate proofs.

use super::super::*;

pub(in super::super) fn construct_lean_order_reflexivity_from_result(
    source_fact: &Fact,
    evidence: &OrderReflexivityBuiltinRuleEvidence,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    if evidence.expected_target.to_string() != source_fact.to_string() {
        return Err("order-reflexivity evidence changed its target".into());
    }
    let Fact::AtomicFact(source_atomic_fact) = source_fact else {
        return Err("order-reflexivity evidence targets a non-atomic fact".into());
    };
    let (left, right) = match source_atomic_fact {
        AtomicFact::LessEqualFact(fact) => (&fact.left, &fact.right),
        AtomicFact::GreaterEqualFact(fact) => (&fact.left, &fact.right),
        AtomicFact::NotLessFact(fact) => (&fact.left, &fact.right),
        AtomicFact::NotGreaterFact(fact) => (&fact.left, &fact.right),
        _ => return Err(
            "order-reflexivity evidence requires `x <= x`, `x >= x`, `not x < x`, or `not x > x`"
                .into(),
        ),
    };
    if obj_equality_key(left) != obj_equality_key(right)
        || obj_equality_key(left) != obj_equality_key(&evidence.repeated_object)
    {
        return Err("order-reflexivity evidence changed its repeated object".into());
    }

    construct_lean_order_reflexivity_from_typed_target(source_fact, context)
}

pub(in super::super) fn construct_lean_order_reflexivity_from_typed_target(
    source_fact: &Fact,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    let Fact::AtomicFact(source_atomic_fact) = source_fact else {
        return Err("order-reflexivity target is not atomic".into());
    };
    let (left, right, weak_order) =
        match source_atomic_fact {
            AtomicFact::LessEqualFact(fact) => (&fact.left, &fact.right, true),
            AtomicFact::GreaterEqualFact(fact) => (&fact.left, &fact.right, true),
            AtomicFact::NotLessFact(fact) => (&fact.left, &fact.right, false),
            AtomicFact::NotGreaterFact(fact) => (&fact.left, &fact.right, false),
            _ => return Err(
                "order-reflexivity target requires `x <= x`, `x >= x`, `not x < x`, or `not x > x`"
                    .into(),
            ),
        };
    if obj_equality_key(left) != obj_equality_key(right) {
        return Err("order-reflexivity target changed its repeated object".into());
    }

    // Zero-ended order syntax has a dedicated existential real
    // representation in Lean, so use its already-reviewed numeric bridge.
    if matches!(left, Obj::Number(number) if number.normalized_value == "0") {
        return render_closed_numeric_comparison_fact(source_fact, context);
    }
    let repeated_object = render_numeric_obj(left, context)?;
    if weak_order {
        Ok(format!("Litex.Le.refl {repeated_object}"))
    } else {
        Ok(format!("Litex.Lt.irrefl {repeated_object}"))
    }
}

pub(in super::super) fn construct_lean_registered_reflexive_predicate_from_result(
    source_fact: &Fact,
    evidence: &RegisteredReflexivePredicateBuiltinRuleEvidence,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    if evidence.expected_target.to_string() != source_fact.to_string() {
        return Err("registered reflexive-predicate evidence changed its target".into());
    }
    let Fact::AtomicFact(AtomicFact::NormalAtomicFact(target)) = source_fact else {
        return Err("registered reflexive-predicate evidence targets a non-user predicate".into());
    };
    if target.predicate.to_string() != evidence.predicate_name || target.body.len() != 2 {
        return Err(
            "registered reflexive-predicate evidence changed its predicate or arity".into(),
        );
    }
    if obj_equality_key(&target.body[0]) != obj_equality_key(&target.body[1]) {
        return Err("registered reflexive-predicate evidence retained unequal arguments".into());
    }

    let binding = context
        .registered_reflexive_predicate_theorem_bindings
        .get(&evidence.predicate_name)
        .ok_or_else(|| {
            format!(
                "registered reflexivity theorem for `{}` is not visible in this compiler environment",
                evidence.predicate_name
            )
        })?;
    let parameters = binding
        .forall_fact
        .typed_parameters
        .collect_param_bindings_with_types();
    let [(parameter, ParamType::Set(_))] = parameters.as_slice() else {
        return Err(
            "direct registered reflexivity currently requires one set-valued parameter".into(),
        );
    };
    if !binding.forall_fact.dom_facts.is_empty() || binding.forall_fact.then_facts.len() != 1 {
        return Err("registered reflexivity theorem changed its forall shape".into());
    }
    let Fact::AtomicFact(AtomicFact::NormalAtomicFact(registered_conclusion)) =
        binding.forall_fact.then_facts[0].clone().to_fact()
    else {
        return Err("registered reflexivity theorem has a non-predicate conclusion".into());
    };
    let parameter_object: Obj =
        Identifier::new_bound(parameter.name().to_string(), parameter.as_ref()).into();
    if registered_conclusion.predicate.to_string() != evidence.predicate_name
        || registered_conclusion.body.len() != 2
        || registered_conclusion
            .body
            .iter()
            .any(|argument| obj_equality_key(argument) != obj_equality_key(&parameter_object))
    {
        return Err("registered reflexivity theorem changed its defining conclusion".into());
    }

    // Rendering the target also validates that the predicate definition and
    // target argument are visible in this exact compiler environment.
    render_fact(source_fact, context)?;
    let argument = render_obj(&target.body[0], context)?;
    Ok(format!("{} {argument}", binding.theorem_name))
}

pub(in super::super) fn registered_predicate_property_parameter_objects(
    forall_fact: &ForallFact,
    property_name: &str,
) -> Result<Vec<Obj>, String> {
    let parameters = forall_fact
        .typed_parameters
        .collect_param_bindings_with_types();
    if parameters.len() < 2
        || parameters
            .iter()
            .any(|(_, parameter_type)| !matches!(parameter_type, ParamType::Set(_)))
    {
        return Err(format!(
            "registered {property_name} theorem changed its set-parameter shape"
        ));
    }
    Ok(parameters
        .iter()
        .map(|(parameter, _)| {
            Identifier::new_bound(parameter.name().to_string(), parameter.as_ref()).into()
        })
        .collect())
}

pub(in super::super) fn registered_positive_user_predicate_fact<'a>(
    fact: &'a Fact,
    property_name: &str,
    role: &str,
) -> Result<&'a NormalAtomicFact, String> {
    let Fact::AtomicFact(AtomicFact::NormalAtomicFact(predicate)) = fact else {
        return Err(format!(
            "registered {property_name} theorem retained a non-predicate {role}"
        ));
    };
    Ok(predicate)
}

pub(in super::super) fn registered_predicate_direct_parameter_keys(
    predicate: &NormalAtomicFact,
    parameter_objects: &[Obj],
    property_name: &str,
    role: &str,
) -> Result<Vec<String>, String> {
    if predicate.body.len() != parameter_objects.len() {
        return Err(format!(
            "registered {property_name} theorem changed its {role} arity"
        ));
    }
    let parameter_keys = parameter_objects
        .iter()
        .map(obj_equality_key)
        .collect::<HashSet<_>>();
    let argument_keys = predicate
        .body
        .iter()
        .map(obj_equality_key)
        .collect::<Vec<_>>();
    if argument_keys
        .iter()
        .any(|key| !parameter_keys.contains(key))
        || argument_keys.iter().collect::<HashSet<_>>().len() != parameter_objects.len()
    {
        return Err(format!(
            "registered {property_name} theorem {role} does not use every binder exactly once"
        ));
    }
    Ok(argument_keys)
}

pub(in super::super) fn registered_symmetric_predicate_gather(
    forall_fact: &ForallFact,
    predicate_name: &str,
) -> Result<Vec<usize>, String> {
    let parameter_objects =
        registered_predicate_property_parameter_objects(forall_fact, "symmetry")?;
    let [domain] = forall_fact.dom_facts.as_slice() else {
        return Err("registered symmetry theorem changed its single-domain shape".into());
    };
    let [conclusion] = forall_fact.then_facts.as_slice() else {
        return Err("registered symmetry theorem changed its single-conclusion shape".into());
    };
    let domain = registered_positive_user_predicate_fact(domain, "symmetry", "domain")?;
    let conclusion_fact = conclusion.clone().to_fact();
    let conclusion =
        registered_positive_user_predicate_fact(&conclusion_fact, "symmetry", "conclusion")?;
    if domain.predicate.to_string() != predicate_name
        || conclusion.predicate.to_string() != predicate_name
    {
        return Err("registered symmetry theorem changed its predicate name".into());
    }
    let domain_keys = registered_predicate_direct_parameter_keys(
        domain,
        &parameter_objects,
        "symmetry",
        "domain",
    )?;
    let conclusion_keys = registered_predicate_direct_parameter_keys(
        conclusion,
        &parameter_objects,
        "symmetry",
        "conclusion",
    )?;
    let mut gather = Vec::with_capacity(conclusion_keys.len());
    for key in conclusion_keys {
        gather.push(
            domain_keys
                .iter()
                .position(|domain_key| domain_key == &key)
                .ok_or_else(|| {
                    "registered symmetry theorem conclusion escaped its domain binders".to_string()
                })?,
        );
    }
    if gather
        .iter()
        .enumerate()
        .all(|(index, source)| index == *source)
    {
        return Err("registered symmetry theorem retained the identity permutation".into());
    }
    Ok(gather)
}

pub(in super::super) fn instantiate_registered_positive_user_predicate_pattern(
    pattern: &NormalAtomicFact,
    parameter_substitution: &HashMap<String, Obj>,
    predicate_name: &str,
    property_name: &str,
    role: &str,
) -> Result<Fact, String> {
    if pattern.predicate.to_string() != predicate_name {
        return Err(format!(
            "registered {property_name} theorem changed its {role} predicate"
        ));
    }
    let arguments = pattern
        .body
        .iter()
        .enumerate()
        .map(|(index, argument)| {
            parameter_substitution
                .get(&obj_equality_key(argument))
                .cloned()
                .ok_or_else(|| {
                    format!(
                        "registered {property_name} theorem {role} argument {index} is not a direct binder"
                    )
                })
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(NormalAtomicFact::new(
        pattern.predicate.clone(),
        arguments,
        pattern.line_file.clone(),
    )
    .into())
}

pub(in super::super) fn instantiate_registered_symmetric_predicate_transition(
    forall_fact: &ForallFact,
    predicate_name: &str,
    current_domain: &Fact,
) -> Result<(Fact, Vec<Obj>), String> {
    let parameter_objects =
        registered_predicate_property_parameter_objects(forall_fact, "symmetry")?;
    let [domain] = forall_fact.dom_facts.as_slice() else {
        return Err("registered symmetry theorem changed its single-domain shape".into());
    };
    let [conclusion] = forall_fact.then_facts.as_slice() else {
        return Err("registered symmetry theorem changed its single-conclusion shape".into());
    };
    let domain = registered_positive_user_predicate_fact(domain, "symmetry", "domain")?;
    let current_domain =
        registered_positive_user_predicate_fact(current_domain, "symmetry", "use premise")?;
    if domain.predicate.to_string() != predicate_name
        || current_domain.predicate.to_string() != predicate_name
        || domain.body.len() != current_domain.body.len()
    {
        return Err("registered symmetry theorem does not match its retained premise".into());
    }
    registered_predicate_direct_parameter_keys(domain, &parameter_objects, "symmetry", "domain")?;
    let mut substitution = HashMap::new();
    for (binder, argument) in domain.body.iter().zip(current_domain.body.iter()) {
        if substitution
            .insert(obj_equality_key(binder), argument.clone())
            .is_some()
        {
            return Err("registered symmetry theorem repeated a domain binder".into());
        }
    }
    let parameter_arguments = parameter_objects
        .iter()
        .map(|parameter| {
            substitution
                .get(&obj_equality_key(parameter))
                .cloned()
                .ok_or_else(|| {
                    "registered symmetry theorem lost a parameter substitution".to_string()
                })
        })
        .collect::<Result<Vec<_>, _>>()?;
    let conclusion_fact = conclusion.clone().to_fact();
    let conclusion =
        registered_positive_user_predicate_fact(&conclusion_fact, "symmetry", "conclusion")?;
    let instantiated_conclusion = instantiate_registered_positive_user_predicate_pattern(
        conclusion,
        &substitution,
        predicate_name,
        "symmetry",
        "conclusion",
    )?;
    Ok((instantiated_conclusion, parameter_arguments))
}

pub(in super::super) fn instantiate_registered_antisymmetric_predicate_application(
    forall_fact: &ForallFact,
    predicate_name: &str,
    target: &Fact,
) -> Result<(Vec<Obj>, Vec<Fact>), String> {
    let parameter_objects =
        registered_predicate_property_parameter_objects(forall_fact, "antisymmetry")?;
    if parameter_objects.len() != 2 || forall_fact.dom_facts.len() != 2 {
        return Err("registered antisymmetry theorem changed its binary domain shape".into());
    }
    let [conclusion] = forall_fact.then_facts.as_slice() else {
        return Err("registered antisymmetry theorem changed its single-conclusion shape".into());
    };
    let conclusion_fact = conclusion.clone().to_fact();
    let Fact::AtomicFact(AtomicFact::EqualFact(conclusion_equality)) = &conclusion_fact else {
        return Err("registered antisymmetry theorem retained a non-equality conclusion".into());
    };
    let Fact::AtomicFact(AtomicFact::EqualFact(target_equality)) = target else {
        return Err(
            "registered antisymmetric-predicate evidence targets a non-equality fact".into(),
        );
    };
    let parameter_keys = parameter_objects
        .iter()
        .map(obj_equality_key)
        .collect::<HashSet<_>>();
    let conclusion_keys = [
        obj_equality_key(&conclusion_equality.left),
        obj_equality_key(&conclusion_equality.right),
    ];
    if conclusion_keys[0] == conclusion_keys[1]
        || conclusion_keys
            .iter()
            .any(|key| !parameter_keys.contains(key))
    {
        return Err(
            "registered antisymmetry theorem conclusion does not use both binders exactly once"
                .into(),
        );
    }
    let mut substitution = HashMap::new();
    substitution.insert(conclusion_keys[0].clone(), target_equality.left.clone());
    substitution.insert(conclusion_keys[1].clone(), target_equality.right.clone());
    let parameter_arguments = parameter_objects
        .iter()
        .map(|parameter| {
            substitution
                .get(&obj_equality_key(parameter))
                .cloned()
                .ok_or_else(|| {
                    "registered antisymmetry theorem lost a parameter substitution".to_string()
                })
        })
        .collect::<Result<Vec<_>, _>>()?;
    let expected_premises = forall_fact
        .dom_facts
        .iter()
        .enumerate()
        .map(|(index, premise)| {
            let premise = registered_positive_user_predicate_fact(
                premise,
                "antisymmetry",
                &format!("domain {index}"),
            )?;
            if premise.body.len() != 2 {
                return Err(format!(
                    "registered antisymmetry theorem changed domain {index} arity"
                ));
            }
            instantiate_registered_positive_user_predicate_pattern(
                premise,
                &substitution,
                predicate_name,
                "antisymmetry",
                &format!("domain {index}"),
            )
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok((parameter_arguments, expected_premises))
}

pub(in super::super) fn instantiate_registered_transitive_predicate_application(
    forall_fact: &ForallFact,
    predicate_name: &str,
    left_premise: &Fact,
    right_premise: &Fact,
) -> Result<(Fact, Vec<Obj>), String> {
    let parameter_objects =
        registered_predicate_property_parameter_objects(forall_fact, "transitivity")?;
    if parameter_objects.len() != 3 || forall_fact.dom_facts.len() != 2 {
        return Err(
            "registered transitivity theorem changed its ternary binder/domain shape".into(),
        );
    }
    let [conclusion] = forall_fact.then_facts.as_slice() else {
        return Err("registered transitivity theorem changed its single-conclusion shape".into());
    };
    let domain_patterns = forall_fact
        .dom_facts
        .iter()
        .enumerate()
        .map(|(index, premise)| {
            registered_positive_user_predicate_fact(
                premise,
                "transitivity",
                &format!("domain {index}"),
            )
        })
        .collect::<Result<Vec<_>, _>>()?;
    let actual_premises = [
        registered_positive_user_predicate_fact(left_premise, "transitivity", "left use premise")?,
        registered_positive_user_predicate_fact(
            right_premise,
            "transitivity",
            "right use premise",
        )?,
    ];
    let parameter_keys = parameter_objects
        .iter()
        .map(obj_equality_key)
        .collect::<HashSet<_>>();
    let mut substitution = HashMap::new();
    for (domain_index, (pattern, actual)) in domain_patterns
        .iter()
        .zip(actual_premises.iter())
        .enumerate()
    {
        if pattern.predicate.to_string() != predicate_name
            || actual.predicate.to_string() != predicate_name
            || pattern.body.len() != 2
            || actual.body.len() != 2
        {
            return Err(format!(
                "registered transitivity theorem changed domain {domain_index} predicate or arity"
            ));
        }
        for (argument_index, (binder, argument)) in
            pattern.body.iter().zip(actual.body.iter()).enumerate()
        {
            let binder_key = obj_equality_key(binder);
            if !parameter_keys.contains(&binder_key) {
                return Err(format!(
                    "registered transitivity domain {domain_index} argument {argument_index} is not a direct binder"
                ));
            }
            if let Some(previous) = substitution.get(&binder_key) {
                if obj_equality_key(previous) != obj_equality_key(argument) {
                    return Err(
                        "registered transitivity premises disagree at their shared binder".into(),
                    );
                }
            } else {
                substitution.insert(binder_key, argument.clone());
            }
        }
    }
    let parameter_arguments = parameter_objects
        .iter()
        .map(|parameter| {
            substitution
                .get(&obj_equality_key(parameter))
                .cloned()
                .ok_or_else(|| {
                    "registered transitivity theorem lost a parameter substitution".to_string()
                })
        })
        .collect::<Result<Vec<_>, _>>()?;
    let conclusion_fact = conclusion.clone().to_fact();
    let conclusion_pattern =
        registered_positive_user_predicate_fact(&conclusion_fact, "transitivity", "conclusion")?;
    if conclusion_pattern.body.len() != 2 {
        return Err("registered transitivity theorem changed its conclusion arity".into());
    }
    let instantiated_conclusion = instantiate_registered_positive_user_predicate_pattern(
        conclusion_pattern,
        &substitution,
        predicate_name,
        "transitivity",
        "conclusion",
    )?;
    Ok((instantiated_conclusion, parameter_arguments))
}
