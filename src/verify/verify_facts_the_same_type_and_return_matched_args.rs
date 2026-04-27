use crate::prelude::*;

impl Runtime {
    pub fn _verify_or_and_chain_atomic_facts_the_same_type_and_return_matched_args(
        fact: &OrAndChainAtomicFact,
        other: &OrAndChainAtomicFact,
    ) -> Result<Option<Vec<(Obj, Obj)>>, RuntimeError> {
        match fact {
            OrAndChainAtomicFact::AndFact(f) => match other {
                OrAndChainAtomicFact::AndFact(other) => {
                    Self::_verify_and_fact_the_same_type_and_return_matched_args(f, other)
                }
                _ => Ok(None),
            },
            OrAndChainAtomicFact::OrFact(f) => match other {
                OrAndChainAtomicFact::OrFact(other) => {
                    Self::_verify_or_fact_the_same_type_and_return_matched_args(f, other)
                }
                _ => Ok(None),
            },
            OrAndChainAtomicFact::AtomicFact(f) => match other {
                OrAndChainAtomicFact::AtomicFact(other) => {
                    Self::_verify_atomic_fact_the_same_type_and_return_matched_args(f, other)
                }
                _ => Ok(None),
            },
            OrAndChainAtomicFact::ChainFact(f) => match other {
                OrAndChainAtomicFact::ChainFact(other) => {
                    Self::_verify_chain_fact_the_same_type_and_return_matched_args(f, other)
                }
                _ => Ok(None),
            },
        }
    }

    pub fn _verify_and_chain_atomic_facts_the_same_type_and_return_matched_args(
        fact: &AndChainAtomicFact,
        other: &AndChainAtomicFact,
    ) -> Result<Option<Vec<(Obj, Obj)>>, RuntimeError> {
        match fact {
            AndChainAtomicFact::AndFact(f) => match other {
                AndChainAtomicFact::AndFact(other) => {
                    Self::_verify_and_fact_the_same_type_and_return_matched_args(f, other)
                }
                _ => Ok(None),
            },
            AndChainAtomicFact::AtomicFact(f) => match other {
                AndChainAtomicFact::AtomicFact(other) => {
                    Self::_verify_atomic_fact_the_same_type_and_return_matched_args(f, other)
                }
                _ => Ok(None),
            },
            AndChainAtomicFact::ChainFact(f) => match other {
                AndChainAtomicFact::ChainFact(other) => {
                    Self::_verify_chain_fact_the_same_type_and_return_matched_args(f, other)
                }
                _ => Ok(None),
            },
        }
    }

    pub fn _verify_chain_fact_the_same_type_and_return_matched_args(
        fact: &ChainFact,
        other: &ChainFact,
    ) -> Result<Option<Vec<(Obj, Obj)>>, RuntimeError> {
        if fact.prop_names.len() != other.prop_names.len() {
            return Ok(None);
        }
        if fact.objs.len() != other.objs.len() {
            return Ok(None);
        }

        for (fact_prop_name, other_prop_name) in fact.prop_names.iter().zip(other.prop_names.iter())
        {
            if fact_prop_name.to_string() != other_prop_name.to_string() {
                return Ok(None);
            }
        }

        let mut matched_args: Vec<(Obj, Obj)> = Vec::new();
        for (fact_obj, other_obj) in fact.objs.iter().zip(other.objs.iter()) {
            matched_args.push((fact_obj.clone(), other_obj.clone()));
        }

        Ok(Some(matched_args))
    }

    pub fn _verify_or_fact_the_same_type_and_return_matched_args(
        fact: &OrFact,
        other: &OrFact,
    ) -> Result<Option<Vec<(Obj, Obj)>>, RuntimeError> {
        if fact.facts.len() != other.facts.len() {
            return Ok(None);
        }

        let mut matched_args: Vec<(Obj, Obj)> = Vec::new();
        for (fact_item, other_item) in fact.facts.iter().zip(other.facts.iter()) {
            let sub_matched_args =
                match Self::_verify_and_chain_atomic_facts_the_same_type_and_return_matched_args(
                    fact_item, other_item,
                )? {
                    Some(value) => value,
                    None => return Ok(None),
                };
            for matched_arg in sub_matched_args {
                matched_args.push(matched_arg);
            }
        }

        Ok(Some(matched_args))
    }

    pub fn _verify_and_fact_the_same_type_and_return_matched_args(
        fact: &AndFact,
        other: &AndFact,
    ) -> Result<Option<Vec<(Obj, Obj)>>, RuntimeError> {
        if fact.facts.len() != other.facts.len() {
            return Ok(None);
        }

        let mut matched_args: Vec<(Obj, Obj)> = Vec::new();
        for (fact_item, other_item) in fact.facts.iter().zip(other.facts.iter()) {
            let sub_matched_args =
                match Self::_verify_atomic_fact_the_same_type_and_return_matched_args(
                    fact_item, other_item,
                )? {
                    Some(value) => value,
                    None => return Ok(None),
                };
            for matched_arg in sub_matched_args {
                matched_args.push(matched_arg);
            }
        }

        Ok(Some(matched_args))
    }

    pub fn _verify_exist_fact_the_same_type_and_return_matched_args(
        fact: &ExistFactEnum,
        other: &ExistFactEnum,
    ) -> Result<Option<Vec<(Obj, Obj)>>, RuntimeError> {
        if fact.is_exist_unique() != other.is_exist_unique() {
            return Ok(None);
        }
        if fact.params_def_with_type().groups.len() != other.params_def_with_type().groups.len() {
            return Ok(None);
        }
        if fact.facts().len() != other.facts().len() {
            return Ok(None);
        }

        let mut matched_args: Vec<(Obj, Obj)> = Vec::new();

        for (fact_param_def, other_param_def) in fact
            .params_def_with_type()
            .groups
            .iter()
            .zip(other.params_def_with_type().groups.iter())
        {
            if fact_param_def.params.len() != other_param_def.params.len() {
                return Ok(None);
            }

            match &fact_param_def.param_type {
                ParamType::Obj(ref obj) => match &other_param_def.param_type {
                    ParamType::Obj(other_obj) => match (obj, other_obj) {
                        (Obj::FamilyObj(family), Obj::FamilyObj(other_family)) => {
                            if family.name.to_string() != other_family.name.to_string() {
                                return Ok(None);
                            }
                            if family.params.len() != other_family.params.len() {
                                return Ok(None);
                            }
                            for (param, other_param) in
                                family.params.iter().zip(other_family.params.iter())
                            {
                                matched_args.push((param.clone(), other_param.clone()));
                            }
                        }
                        _ => {
                            matched_args.push((obj.clone(), other_obj.clone()));
                        }
                    },
                    _ => return Ok(None),
                },
                ParamType::Set(_) => match &other_param_def.param_type {
                    ParamType::Set(_) => {}
                    _ => return Ok(None),
                },
                ParamType::NonemptySet(_) => match &other_param_def.param_type {
                    ParamType::NonemptySet(_) => {}
                    _ => return Ok(None),
                },
                ParamType::FiniteSet(_) => match &other_param_def.param_type {
                    ParamType::FiniteSet(_) => {}
                    _ => return Ok(None),
                },
            }
        }
        for (fact_item, other_item) in fact.facts().iter().zip(other.facts().iter()) {
            let sub_matched_args =
                match Self::_verify_or_and_chain_atomic_facts_the_same_type_and_return_matched_args(
                    fact_item, other_item,
                )? {
                    Some(value) => value,
                    None => return Ok(None),
                };
            for matched_arg in sub_matched_args {
                matched_args.push(matched_arg);
            }
        }

        Ok(Some(matched_args))
    }

    pub fn _verify_atomic_fact_the_same_type_and_return_matched_args(
        _fact: &AtomicFact,
        _other: &AtomicFact,
    ) -> Result<Option<Vec<(Obj, Obj)>>, RuntimeError> {
        match _fact {
            AtomicFact::NormalAtomicFact(fact_normal_atomic_fact) => match _other {
                AtomicFact::NormalAtomicFact(other_normal_atomic_fact) => {
                    if fact_normal_atomic_fact.predicate.to_string()
                        != other_normal_atomic_fact.predicate.to_string()
                    {
                        return Ok(None);
                    }
                    if fact_normal_atomic_fact.body.len() != other_normal_atomic_fact.body.len() {
                        return Ok(None);
                    }

                    let mut matched_args: Vec<(Obj, Obj)> =
                        Vec::with_capacity(fact_normal_atomic_fact.body.len());
                    for (fact_arg, other_arg) in fact_normal_atomic_fact
                        .body
                        .iter()
                        .zip(other_normal_atomic_fact.body.iter())
                    {
                        matched_args.push((fact_arg.clone(), other_arg.clone()));
                    }
                    Ok(Some(matched_args))
                }
                AtomicFact::NotNormalAtomicFact(other_not_normal_atomic_fact) => {
                    if fact_normal_atomic_fact.predicate.to_string()
                        != other_not_normal_atomic_fact.predicate.to_string()
                    {
                        return Ok(None);
                    }
                    if fact_normal_atomic_fact.body.len() != other_not_normal_atomic_fact.body.len()
                    {
                        return Ok(None);
                    }

                    let mut matched_args: Vec<(Obj, Obj)> =
                        Vec::with_capacity(fact_normal_atomic_fact.body.len());
                    for (fact_arg, other_arg) in fact_normal_atomic_fact
                        .body
                        .iter()
                        .zip(other_not_normal_atomic_fact.body.iter())
                    {
                        matched_args.push((fact_arg.clone(), other_arg.clone()));
                    }
                    Ok(Some(matched_args))
                }
                _ => Ok(None),
            },
            AtomicFact::EqualFact(f) => match _other {
                AtomicFact::EqualFact(other) => {
                    let matched_args = vec![
                        (f.left.clone(), other.left.clone()),
                        (f.right.clone(), other.right.clone()),
                    ];
                    return Ok(Some(matched_args));
                }
                _ => Ok(None),
            },
            AtomicFact::NotNormalAtomicFact(fact_not_normal_atomic_fact) => match _other {
                AtomicFact::NotNormalAtomicFact(other_not_normal_atomic_fact) => {
                    if fact_not_normal_atomic_fact.predicate.to_string()
                        != other_not_normal_atomic_fact.predicate.to_string()
                    {
                        return Ok(None);
                    }
                    if fact_not_normal_atomic_fact.body.len()
                        != other_not_normal_atomic_fact.body.len()
                    {
                        return Ok(None);
                    }

                    let mut matched_args: Vec<(Obj, Obj)> =
                        Vec::with_capacity(fact_not_normal_atomic_fact.body.len());
                    for (fact_arg, other_arg) in fact_not_normal_atomic_fact
                        .body
                        .iter()
                        .zip(other_not_normal_atomic_fact.body.iter())
                    {
                        matched_args.push((fact_arg.clone(), other_arg.clone()));
                    }
                    Ok(Some(matched_args))
                }
                AtomicFact::NormalAtomicFact(other_normal_atomic_fact) => {
                    if fact_not_normal_atomic_fact.predicate.to_string()
                        != other_normal_atomic_fact.predicate.to_string()
                    {
                        return Ok(None);
                    }
                    if fact_not_normal_atomic_fact.body.len() != other_normal_atomic_fact.body.len()
                    {
                        return Ok(None);
                    }

                    let mut matched_args: Vec<(Obj, Obj)> =
                        Vec::with_capacity(fact_not_normal_atomic_fact.body.len());
                    for (fact_arg, other_arg) in fact_not_normal_atomic_fact
                        .body
                        .iter()
                        .zip(other_normal_atomic_fact.body.iter())
                    {
                        matched_args.push((fact_arg.clone(), other_arg.clone()));
                    }
                    Ok(Some(matched_args))
                }
                _ => Ok(None),
            },
            AtomicFact::NotEqualFact(fact_not_equal_fact) => match _other {
                AtomicFact::NotEqualFact(other_not_equal_fact) => Ok(Some(vec![
                    (
                        fact_not_equal_fact.left.clone(),
                        other_not_equal_fact.left.clone(),
                    ),
                    (
                        fact_not_equal_fact.right.clone(),
                        other_not_equal_fact.right.clone(),
                    ),
                ])),
                _ => Ok(None),
            },
            AtomicFact::LessFact(fact_less_fact) => match _other {
                AtomicFact::LessFact(other_less_fact) => Ok(Some(vec![
                    (fact_less_fact.left.clone(), other_less_fact.left.clone()),
                    (fact_less_fact.right.clone(), other_less_fact.right.clone()),
                ])),
                _ => Ok(None),
            },
            AtomicFact::NotLessFact(fact_not_less_fact) => match _other {
                AtomicFact::NotLessFact(other_not_less_fact) => Ok(Some(vec![
                    (
                        fact_not_less_fact.left.clone(),
                        other_not_less_fact.left.clone(),
                    ),
                    (
                        fact_not_less_fact.right.clone(),
                        other_not_less_fact.right.clone(),
                    ),
                ])),
                _ => Ok(None),
            },
            AtomicFact::GreaterFact(fact_greater_fact) => match _other {
                AtomicFact::GreaterFact(other_greater_fact) => Ok(Some(vec![
                    (
                        fact_greater_fact.left.clone(),
                        other_greater_fact.left.clone(),
                    ),
                    (
                        fact_greater_fact.right.clone(),
                        other_greater_fact.right.clone(),
                    ),
                ])),
                _ => Ok(None),
            },
            AtomicFact::NotGreaterFact(fact_not_greater_fact) => match _other {
                AtomicFact::NotGreaterFact(other_not_greater_fact) => Ok(Some(vec![
                    (
                        fact_not_greater_fact.left.clone(),
                        other_not_greater_fact.left.clone(),
                    ),
                    (
                        fact_not_greater_fact.right.clone(),
                        other_not_greater_fact.right.clone(),
                    ),
                ])),
                _ => Ok(None),
            },
            AtomicFact::LessEqualFact(fact_less_equal_fact) => match _other {
                AtomicFact::LessEqualFact(other_less_equal_fact) => Ok(Some(vec![
                    (
                        fact_less_equal_fact.left.clone(),
                        other_less_equal_fact.left.clone(),
                    ),
                    (
                        fact_less_equal_fact.right.clone(),
                        other_less_equal_fact.right.clone(),
                    ),
                ])),
                _ => Ok(None),
            },
            AtomicFact::NotLessEqualFact(fact_not_less_equal_fact) => match _other {
                AtomicFact::NotLessEqualFact(other_not_less_equal_fact) => Ok(Some(vec![
                    (
                        fact_not_less_equal_fact.left.clone(),
                        other_not_less_equal_fact.left.clone(),
                    ),
                    (
                        fact_not_less_equal_fact.right.clone(),
                        other_not_less_equal_fact.right.clone(),
                    ),
                ])),
                _ => Ok(None),
            },
            AtomicFact::GreaterEqualFact(fact_greater_equal_fact) => match _other {
                AtomicFact::GreaterEqualFact(other_greater_equal_fact) => Ok(Some(vec![
                    (
                        fact_greater_equal_fact.left.clone(),
                        other_greater_equal_fact.left.clone(),
                    ),
                    (
                        fact_greater_equal_fact.right.clone(),
                        other_greater_equal_fact.right.clone(),
                    ),
                ])),
                _ => Ok(None),
            },
            AtomicFact::NotGreaterEqualFact(fact_not_greater_equal_fact) => match _other {
                AtomicFact::NotGreaterEqualFact(other_not_greater_equal_fact) => Ok(Some(vec![
                    (
                        fact_not_greater_equal_fact.left.clone(),
                        other_not_greater_equal_fact.left.clone(),
                    ),
                    (
                        fact_not_greater_equal_fact.right.clone(),
                        other_not_greater_equal_fact.right.clone(),
                    ),
                ])),
                _ => Ok(None),
            },
            AtomicFact::IsSetFact(fact_is_set_fact) => match _other {
                AtomicFact::IsSetFact(other_is_set_fact) => Ok(Some(vec![(
                    fact_is_set_fact.set.clone(),
                    other_is_set_fact.set.clone(),
                )])),
                _ => Ok(None),
            },
            AtomicFact::NotIsSetFact(fact_not_is_set_fact) => match _other {
                AtomicFact::NotIsSetFact(other_not_is_set_fact) => Ok(Some(vec![(
                    fact_not_is_set_fact.set.clone(),
                    other_not_is_set_fact.set.clone(),
                )])),
                _ => Ok(None),
            },
            AtomicFact::IsNonemptySetFact(fact_is_nonempty_set_fact) => match _other {
                AtomicFact::IsNonemptySetFact(other_is_nonempty_set_fact) => Ok(Some(vec![(
                    fact_is_nonempty_set_fact.set.clone(),
                    other_is_nonempty_set_fact.set.clone(),
                )])),
                _ => Ok(None),
            },
            AtomicFact::NotIsNonemptySetFact(fact_not_is_nonempty_set_fact) => match _other {
                AtomicFact::NotIsNonemptySetFact(other_not_is_nonempty_set_fact) => {
                    Ok(Some(vec![(
                        fact_not_is_nonempty_set_fact.set.clone(),
                        other_not_is_nonempty_set_fact.set.clone(),
                    )]))
                }
                _ => Ok(None),
            },
            AtomicFact::IsFiniteSetFact(fact_is_finite_set_fact) => match _other {
                AtomicFact::IsFiniteSetFact(other_is_finite_set_fact) => Ok(Some(vec![(
                    fact_is_finite_set_fact.set.clone(),
                    other_is_finite_set_fact.set.clone(),
                )])),
                _ => Ok(None),
            },
            AtomicFact::NotIsFiniteSetFact(fact_not_is_finite_set_fact) => match _other {
                AtomicFact::NotIsFiniteSetFact(other_not_is_finite_set_fact) => Ok(Some(vec![(
                    fact_not_is_finite_set_fact.set.clone(),
                    other_not_is_finite_set_fact.set.clone(),
                )])),
                _ => Ok(None),
            },
            AtomicFact::InFact(fact_in_fact) => match _other {
                AtomicFact::InFact(other_in_fact) => Ok(Some(vec![
                    (fact_in_fact.element.clone(), other_in_fact.element.clone()),
                    (fact_in_fact.set.clone(), other_in_fact.set.clone()),
                ])),
                _ => Ok(None),
            },
            AtomicFact::NotInFact(fact_not_in_fact) => match _other {
                AtomicFact::NotInFact(other_not_in_fact) => Ok(Some(vec![
                    (
                        fact_not_in_fact.element.clone(),
                        other_not_in_fact.element.clone(),
                    ),
                    (fact_not_in_fact.set.clone(), other_not_in_fact.set.clone()),
                ])),
                _ => Ok(None),
            },
            AtomicFact::IsCartFact(fact_is_cart_fact) => match _other {
                AtomicFact::IsCartFact(other_is_cart_fact) => Ok(Some(vec![(
                    fact_is_cart_fact.set.clone(),
                    other_is_cart_fact.set.clone(),
                )])),
                _ => Ok(None),
            },
            AtomicFact::NotIsCartFact(fact_not_is_cart_fact) => match _other {
                AtomicFact::NotIsCartFact(other_not_is_cart_fact) => Ok(Some(vec![(
                    fact_not_is_cart_fact.set.clone(),
                    other_not_is_cart_fact.set.clone(),
                )])),
                _ => Ok(None),
            },
            AtomicFact::IsTupleFact(fact_is_tuple_fact) => match _other {
                AtomicFact::IsTupleFact(other_is_tuple_fact) => Ok(Some(vec![(
                    fact_is_tuple_fact.set.clone(),
                    other_is_tuple_fact.set.clone(),
                )])),
                _ => Ok(None),
            },
            AtomicFact::NotIsTupleFact(fact_not_is_tuple_fact) => match _other {
                AtomicFact::NotIsTupleFact(other_not_is_tuple_fact) => Ok(Some(vec![(
                    fact_not_is_tuple_fact.set.clone(),
                    other_not_is_tuple_fact.set.clone(),
                )])),
                _ => Ok(None),
            },
            AtomicFact::SubsetFact(fact_subset_fact) => match _other {
                AtomicFact::SubsetFact(other_subset_fact) => Ok(Some(vec![
                    (
                        fact_subset_fact.left.clone(),
                        other_subset_fact.left.clone(),
                    ),
                    (
                        fact_subset_fact.right.clone(),
                        other_subset_fact.right.clone(),
                    ),
                ])),
                _ => Ok(None),
            },
            AtomicFact::NotSubsetFact(fact_not_subset_fact) => match _other {
                AtomicFact::NotSubsetFact(other_not_subset_fact) => Ok(Some(vec![
                    (
                        fact_not_subset_fact.left.clone(),
                        other_not_subset_fact.left.clone(),
                    ),
                    (
                        fact_not_subset_fact.right.clone(),
                        other_not_subset_fact.right.clone(),
                    ),
                ])),
                _ => Ok(None),
            },
            AtomicFact::SupersetFact(fact_superset_fact) => match _other {
                AtomicFact::SupersetFact(other_superset_fact) => Ok(Some(vec![
                    (
                        fact_superset_fact.left.clone(),
                        other_superset_fact.left.clone(),
                    ),
                    (
                        fact_superset_fact.right.clone(),
                        other_superset_fact.right.clone(),
                    ),
                ])),
                _ => Ok(None),
            },
            AtomicFact::NotSupersetFact(fact_not_superset_fact) => match _other {
                AtomicFact::NotSupersetFact(other_not_superset_fact) => Ok(Some(vec![
                    (
                        fact_not_superset_fact.left.clone(),
                        other_not_superset_fact.left.clone(),
                    ),
                    (
                        fact_not_superset_fact.right.clone(),
                        other_not_superset_fact.right.clone(),
                    ),
                ])),
                _ => Ok(None),
            },
            AtomicFact::RestrictFact(fact_restrict_fact) => match _other {
                AtomicFact::RestrictFact(other_restrict_fact) => Ok(Some(vec![
                    (
                        fact_restrict_fact.obj.clone(),
                        other_restrict_fact.obj.clone(),
                    ),
                    (
                        fact_restrict_fact.obj_can_restrict_to_fn_set.clone(),
                        other_restrict_fact.obj_can_restrict_to_fn_set.clone(),
                    ),
                ])),
                _ => Ok(None),
            },
            AtomicFact::NotRestrictFact(fact_not_restrict_fact) => match _other {
                AtomicFact::NotRestrictFact(other_not_restrict_fact) => Ok(Some(vec![
                    (
                        fact_not_restrict_fact.obj.clone(),
                        other_not_restrict_fact.obj.clone(),
                    ),
                    (
                        fact_not_restrict_fact.obj_cannot_restrict_to_fn_set.clone(),
                        other_not_restrict_fact
                            .obj_cannot_restrict_to_fn_set
                            .clone(),
                    ),
                ])),
                _ => Ok(None),
            },
            AtomicFact::FnEqualOnFact(f) => match _other {
                AtomicFact::FnEqualOnFact(o) => Ok(Some(vec![
                    (f.left.clone(), o.left.clone()),
                    (f.right.clone(), o.right.clone()),
                    (f.set.clone(), o.set.clone()),
                ])),
                _ => Ok(None),
            },
        }
    }
}
