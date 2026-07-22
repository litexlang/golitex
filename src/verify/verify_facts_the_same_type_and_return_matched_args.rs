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
        &self,
        fact: &ExistFactEnum,
        other: &ExistFactEnum,
    ) -> Result<Option<Vec<(Obj, Obj)>>, RuntimeError> {
        let mut next_forall_scope_id = 0;
        self._verify_exist_fact_the_same_type_and_return_matched_args_with_scope_counter(
            fact,
            other,
            &mut next_forall_scope_id,
        )
    }

    fn _verify_exist_fact_the_same_type_and_return_matched_args_with_scope_counter(
        &self,
        fact: &ExistFactEnum,
        other: &ExistFactEnum,
        next_forall_scope_id: &mut usize,
    ) -> Result<Option<Vec<(Obj, Obj)>>, RuntimeError> {
        if fact.is_not_exist() != other.is_not_exist() {
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
                    ParamType::Obj(other_obj) => {
                        matched_args.push((obj.clone(), other_obj.clone()))
                    }
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
            let sub_matched_args = match self
                ._verify_exist_body_facts_the_same_type_and_return_matched_args(
                    fact_item,
                    other_item,
                    next_forall_scope_id,
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

    fn _verify_exist_body_facts_the_same_type_and_return_matched_args(
        &self,
        fact: &ExistBodyFact,
        other: &ExistBodyFact,
        next_forall_scope_id: &mut usize,
    ) -> Result<Option<Vec<(Obj, Obj)>>, RuntimeError> {
        match (fact, other) {
            (ExistBodyFact::AtomicFact(a), ExistBodyFact::AtomicFact(b)) => {
                Self::_verify_atomic_fact_the_same_type_and_return_matched_args(a, b)
            }
            (ExistBodyFact::AndFact(a), ExistBodyFact::AndFact(b)) => {
                Self::_verify_and_fact_the_same_type_and_return_matched_args(a, b)
            }
            (ExistBodyFact::ChainFact(a), ExistBodyFact::ChainFact(b)) => {
                Self::_verify_chain_fact_the_same_type_and_return_matched_args(a, b)
            }
            (ExistBodyFact::OrFact(a), ExistBodyFact::OrFact(b)) => {
                Self::_verify_or_fact_the_same_type_and_return_matched_args(a, b)
            }
            (ExistBodyFact::InlineForall(a), ExistBodyFact::InlineForall(b)) => self
                ._verify_forall_fact_the_same_type_and_return_matched_args(
                    a,
                    b,
                    next_forall_scope_id,
                ),
            _ => Ok(None),
        }
    }

    fn _verify_forall_fact_the_same_type_and_return_matched_args(
        &self,
        fact: &ForallFact,
        other: &ForallFact,
        next_forall_scope_id: &mut usize,
    ) -> Result<Option<Vec<(Obj, Obj)>>, RuntimeError> {
        if fact.params_def_with_type.groups.len() != other.params_def_with_type.groups.len()
            || fact.dom_facts.len() != other.dom_facts.len()
            || fact.then_facts.len() != other.then_facts.len()
        {
            return Ok(None);
        }

        let fact_names = fact.params_def_with_type.collect_param_names();
        let other_names = other.params_def_with_type.collect_param_names();
        if fact_names.len() != other_names.len() {
            return Ok(None);
        }
        let forall_scope_id = *next_forall_scope_id;
        *next_forall_scope_id += 1;
        let canonical_names: Vec<String> = (0..fact_names.len())
            .map(|index| format!("#forall_match_{}_{}", forall_scope_id, index))
            .collect();
        let fact_map = fact_names
            .iter()
            .cloned()
            .zip(
                canonical_names
                    .iter()
                    .cloned()
                    .map(|name| ForallFreeParamObj::new(name).into()),
            )
            .collect();
        let other_map = other_names
            .iter()
            .cloned()
            .zip(
                canonical_names
                    .iter()
                    .cloned()
                    .map(|name| ForallFreeParamObj::new(name).into()),
            )
            .collect();
        let fact = self.alpha_rename_forall_fact(fact, &fact_map)?;
        let other = self.alpha_rename_forall_fact(other, &other_map)?;

        let mut matched_args = Vec::new();
        for (fact_group, other_group) in fact
            .params_def_with_type
            .groups
            .iter()
            .zip(other.params_def_with_type.groups.iter())
        {
            if fact_group.params.len() != other_group.params.len() {
                return Ok(None);
            }
            match (&fact_group.param_type, &other_group.param_type) {
                (ParamType::Obj(left), ParamType::Obj(right)) => {
                    matched_args.push((left.clone(), right.clone()));
                }
                (ParamType::Set(_), ParamType::Set(_))
                | (ParamType::NonemptySet(_), ParamType::NonemptySet(_))
                | (ParamType::FiniteSet(_), ParamType::FiniteSet(_)) => {}
                _ => return Ok(None),
            }
        }

        for (left, right) in fact.dom_facts.iter().zip(other.dom_facts.iter()) {
            let Some(pairs) = self._verify_fact_the_same_type_and_return_matched_args(
                left,
                right,
                next_forall_scope_id,
            )?
            else {
                return Ok(None);
            };
            matched_args.extend(pairs);
        }
        for (left, right) in fact.then_facts.iter().zip(other.then_facts.iter()) {
            let Some(pairs) = self
                ._verify_exist_or_and_chain_fact_the_same_type_and_return_matched_args(
                    left,
                    right,
                    next_forall_scope_id,
                )?
            else {
                return Ok(None);
            };
            matched_args.extend(pairs);
        }
        Ok(Some(matched_args))
    }

    fn _verify_fact_the_same_type_and_return_matched_args(
        &self,
        fact: &Fact,
        other: &Fact,
        next_forall_scope_id: &mut usize,
    ) -> Result<Option<Vec<(Obj, Obj)>>, RuntimeError> {
        match (fact, other) {
            (Fact::AtomicFact(left), Fact::AtomicFact(right)) => {
                Self::_verify_atomic_fact_the_same_type_and_return_matched_args(left, right)
            }
            (Fact::ExistFact(left), Fact::ExistFact(right)) => self
                ._verify_exist_fact_the_same_type_and_return_matched_args_with_scope_counter(
                    left,
                    right,
                    next_forall_scope_id,
                ),
            (Fact::OrFact(left), Fact::OrFact(right)) => {
                Self::_verify_or_fact_the_same_type_and_return_matched_args(left, right)
            }
            (Fact::AndFact(left), Fact::AndFact(right)) => {
                Self::_verify_and_fact_the_same_type_and_return_matched_args(left, right)
            }
            (Fact::ChainFact(left), Fact::ChainFact(right)) => {
                Self::_verify_chain_fact_the_same_type_and_return_matched_args(left, right)
            }
            (Fact::ForallFact(left), Fact::ForallFact(right)) => self
                ._verify_forall_fact_the_same_type_and_return_matched_args(
                    left,
                    right,
                    next_forall_scope_id,
                ),
            (Fact::ForallFactWithIff(left), Fact::ForallFactWithIff(right)) => {
                let Some(mut pairs) = self
                    ._verify_forall_fact_the_same_type_and_return_matched_args(
                        &left.forall_fact,
                        &right.forall_fact,
                        next_forall_scope_id,
                    )?
                else {
                    return Ok(None);
                };
                if left.iff_facts.len() != right.iff_facts.len() {
                    return Ok(None);
                }
                for (left_iff, right_iff) in left.iff_facts.iter().zip(right.iff_facts.iter()) {
                    let Some(iff_pairs) = self
                        ._verify_exist_or_and_chain_fact_the_same_type_and_return_matched_args(
                            left_iff,
                            right_iff,
                            next_forall_scope_id,
                        )?
                    else {
                        return Ok(None);
                    };
                    pairs.extend(iff_pairs);
                }
                Ok(Some(pairs))
            }
            (Fact::NotForall(left), Fact::NotForall(right)) => self
                ._verify_forall_fact_the_same_type_and_return_matched_args(
                    &left.forall_fact,
                    &right.forall_fact,
                    next_forall_scope_id,
                ),
            _ => Ok(None),
        }
    }

    fn _verify_exist_or_and_chain_fact_the_same_type_and_return_matched_args(
        &self,
        fact: &ExistOrAndChainAtomicFact,
        other: &ExistOrAndChainAtomicFact,
        next_forall_scope_id: &mut usize,
    ) -> Result<Option<Vec<(Obj, Obj)>>, RuntimeError> {
        match (fact, other) {
            (
                ExistOrAndChainAtomicFact::ExistFact(left),
                ExistOrAndChainAtomicFact::ExistFact(right),
            ) => self._verify_exist_fact_the_same_type_and_return_matched_args_with_scope_counter(
                left,
                right,
                next_forall_scope_id,
            ),
            (
                ExistOrAndChainAtomicFact::AtomicFact(left),
                ExistOrAndChainAtomicFact::AtomicFact(right),
            ) => Self::_verify_atomic_fact_the_same_type_and_return_matched_args(left, right),
            (
                ExistOrAndChainAtomicFact::AndFact(left),
                ExistOrAndChainAtomicFact::AndFact(right),
            ) => Self::_verify_and_fact_the_same_type_and_return_matched_args(left, right),
            (
                ExistOrAndChainAtomicFact::ChainFact(left),
                ExistOrAndChainAtomicFact::ChainFact(right),
            ) => Self::_verify_chain_fact_the_same_type_and_return_matched_args(left, right),
            (ExistOrAndChainAtomicFact::OrFact(left), ExistOrAndChainAtomicFact::OrFact(right)) => {
                Self::_verify_or_fact_the_same_type_and_return_matched_args(left, right)
            }
            _ => Ok(None),
        }
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
                AtomicFact::NotNormalAtomicFact(_) => Ok(None),
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
                AtomicFact::NormalAtomicFact(_) => Ok(None),
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
            AtomicFact::FnEqualInFact(f) => match _other {
                AtomicFact::FnEqualInFact(o) => Ok(Some(vec![
                    (f.left.clone(), o.left.clone()),
                    (f.right.clone(), o.right.clone()),
                    (f.set.clone(), o.set.clone()),
                ])),
                _ => Ok(None),
            },
            AtomicFact::FnEqualFact(f) => match _other {
                AtomicFact::FnEqualFact(o) => Ok(Some(vec![
                    (f.left.clone(), o.left.clone()),
                    (f.right.clone(), o.right.clone()),
                ])),
                _ => Ok(None),
            },
        }
    }

    pub fn _verify_or_and_chain_atomic_facts_the_same_type_ref(
        fact: &OrAndChainAtomicFact,
        other: &OrAndChainAtomicFact,
    ) -> Result<bool, RuntimeError> {
        match fact {
            OrAndChainAtomicFact::AndFact(f) => match other {
                OrAndChainAtomicFact::AndFact(other) => {
                    Self::_verify_and_fact_the_same_type_ref(f, other)
                }
                _ => Ok(false),
            },
            OrAndChainAtomicFact::OrFact(f) => match other {
                OrAndChainAtomicFact::OrFact(other) => {
                    Self::_verify_or_fact_the_same_type_ref(f, other)
                }
                _ => Ok(false),
            },
            OrAndChainAtomicFact::AtomicFact(f) => match other {
                OrAndChainAtomicFact::AtomicFact(other) => {
                    Self::_verify_atomic_fact_the_same_type_ref(f, other)
                }
                _ => Ok(false),
            },
            OrAndChainAtomicFact::ChainFact(f) => match other {
                OrAndChainAtomicFact::ChainFact(other) => {
                    Self::_verify_chain_fact_the_same_type_ref(f, other)
                }
                _ => Ok(false),
            },
        }
    }

    pub fn _verify_and_chain_atomic_facts_the_same_type_ref(
        fact: &AndChainAtomicFact,
        other: &AndChainAtomicFact,
    ) -> Result<bool, RuntimeError> {
        match fact {
            AndChainAtomicFact::AndFact(f) => match other {
                AndChainAtomicFact::AndFact(other) => {
                    Self::_verify_and_fact_the_same_type_ref(f, other)
                }
                _ => Ok(false),
            },
            AndChainAtomicFact::AtomicFact(f) => match other {
                AndChainAtomicFact::AtomicFact(other) => {
                    Self::_verify_atomic_fact_the_same_type_ref(f, other)
                }
                _ => Ok(false),
            },
            AndChainAtomicFact::ChainFact(f) => match other {
                AndChainAtomicFact::ChainFact(other) => {
                    Self::_verify_chain_fact_the_same_type_ref(f, other)
                }
                _ => Ok(false),
            },
        }
    }

    pub fn _verify_chain_fact_the_same_type_ref(
        fact: &ChainFact,
        other: &ChainFact,
    ) -> Result<bool, RuntimeError> {
        if fact.prop_names.len() != other.prop_names.len() {
            return Ok(false);
        }
        if fact.objs.len() != other.objs.len() {
            return Ok(false);
        }

        for (fact_prop_name, other_prop_name) in fact.prop_names.iter().zip(other.prop_names.iter())
        {
            if fact_prop_name.to_string() != other_prop_name.to_string() {
                return Ok(false);
            }
        }

        Ok(true)
    }

    pub fn _verify_or_fact_the_same_type_ref(
        fact: &OrFact,
        other: &OrFact,
    ) -> Result<bool, RuntimeError> {
        if fact.facts.len() != other.facts.len() {
            return Ok(false);
        }

        for (fact_item, other_item) in fact.facts.iter().zip(other.facts.iter()) {
            if !Self::_verify_and_chain_atomic_facts_the_same_type_ref(fact_item, other_item)? {
                return Ok(false);
            }
        }

        Ok(true)
    }

    pub fn _verify_and_fact_the_same_type_ref(
        fact: &AndFact,
        other: &AndFact,
    ) -> Result<bool, RuntimeError> {
        if fact.facts.len() != other.facts.len() {
            return Ok(false);
        }

        for (fact_item, other_item) in fact.facts.iter().zip(other.facts.iter()) {
            if !Self::_verify_atomic_fact_the_same_type_ref(fact_item, other_item)? {
                return Ok(false);
            }
        }

        Ok(true)
    }

    pub fn _verify_atomic_fact_the_same_type_ref(
        fact: &AtomicFact,
        other: &AtomicFact,
    ) -> Result<bool, RuntimeError> {
        match (fact, other) {
            (
                AtomicFact::NormalAtomicFact(fact_normal_atomic_fact),
                AtomicFact::NormalAtomicFact(other_normal_atomic_fact),
            ) => {
                if fact_normal_atomic_fact.predicate.to_string()
                    != other_normal_atomic_fact.predicate.to_string()
                {
                    return Ok(false);
                }
                if fact_normal_atomic_fact.body.len() != other_normal_atomic_fact.body.len() {
                    return Ok(false);
                }
            }
            (AtomicFact::NormalAtomicFact(_), AtomicFact::NotNormalAtomicFact(_)) => {
                return Ok(false);
            }
            (
                AtomicFact::NotNormalAtomicFact(fact_not_normal_atomic_fact),
                AtomicFact::NotNormalAtomicFact(other_not_normal_atomic_fact),
            ) => {
                if fact_not_normal_atomic_fact.predicate.to_string()
                    != other_not_normal_atomic_fact.predicate.to_string()
                {
                    return Ok(false);
                }
                if fact_not_normal_atomic_fact.body.len() != other_not_normal_atomic_fact.body.len()
                {
                    return Ok(false);
                }
            }
            (AtomicFact::NotNormalAtomicFact(_), AtomicFact::NormalAtomicFact(_)) => {
                return Ok(false);
            }
            _ => {
                if std::mem::discriminant(fact) != std::mem::discriminant(other) {
                    return Ok(false);
                }
            }
        }

        Ok(true)
    }
}
