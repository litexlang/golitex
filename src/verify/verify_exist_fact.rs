use crate::prelude::*;
use std::collections::{HashMap, HashSet};
use std::result::Result;

fn real_line_comparison_exist_fact_non_witness_operands(
    exist_fact: &ExistFactEnum,
) -> Option<Vec<&Obj>> {
    if !exist_fact.is_plain_exist() || exist_fact.facts().len() != 1 {
        return None;
    }

    let param_names = exist_fact.params_def_with_type().collect_param_names();
    if !(param_names.len() == 1 || param_names.len() == 2) {
        return None;
    }
    if !exist_fact
        .params_def_with_type()
        .groups
        .iter()
        .all(|group| {
            matches!(
                &group.param_type,
                ParamType::Obj(Obj::StandardSet(StandardSet::R))
            )
        })
    {
        return None;
    }

    let ExistBodyFact::AtomicFact(atomic_fact) = &exist_fact.facts()[0] else {
        return None;
    };
    let (left, right) = match atomic_fact {
        AtomicFact::EqualFact(fact) => (&fact.left, &fact.right),
        AtomicFact::NotEqualFact(fact) => (&fact.left, &fact.right),
        AtomicFact::LessFact(fact) => (&fact.left, &fact.right),
        AtomicFact::GreaterFact(fact) => (&fact.left, &fact.right),
        AtomicFact::LessEqualFact(fact) => (&fact.left, &fact.right),
        AtomicFact::GreaterEqualFact(fact) => (&fact.left, &fact.right),
        _ => return None,
    };

    let direct_exist_param_name = |obj: &Obj| match obj {
        Obj::Atom(AtomObj::Exist(param)) => Some(param.name.clone()),
        _ => None,
    };

    if param_names.len() == 1 {
        let witness_name = &param_names[0];
        let other = if direct_exist_param_name(left).as_deref() == Some(witness_name.as_str()) {
            right
        } else if direct_exist_param_name(right).as_deref() == Some(witness_name.as_str()) {
            left
        } else {
            return None;
        };
        if Runtime::obj_depends_on_given_exist_param(other, param_names.as_slice()) {
            return None;
        }
        return Some(vec![other]);
    } else {
        let (Some(left_name), Some(right_name)) = (
            direct_exist_param_name(left),
            direct_exist_param_name(right),
        ) else {
            return None;
        };
        if left_name == right_name
            || !param_names.iter().any(|name| name == &left_name)
            || !param_names.iter().any(|name| name == &right_name)
        {
            return None;
        }
    }

    Some(vec![])
}

fn rational_integer_ratio_exist_fact_non_witness_operand(
    exist_fact: &ExistFactEnum,
) -> Option<&Obj> {
    if !exist_fact.is_plain_exist() || exist_fact.facts().len() != 1 {
        return None;
    }

    let params = exist_fact
        .params_def_with_type()
        .collect_param_names_with_types();
    if params.len() != 2 {
        return None;
    }
    let (numerator_name, numerator_type) = &params[0];
    let (denominator_name, denominator_type) = &params[1];
    if !matches!(
        numerator_type,
        ParamType::Obj(Obj::StandardSet(StandardSet::Z))
    ) || !matches!(
        denominator_type,
        ParamType::Obj(Obj::StandardSet(StandardSet::ZStar))
    ) {
        return None;
    }

    let ExistBodyFact::AtomicFact(AtomicFact::EqualFact(equal_fact)) = &exist_fact.facts()[0]
    else {
        return None;
    };

    let is_selected_ratio = |obj: &Obj| match obj {
        Obj::Div(div) => {
            matches!(
                div.left.as_ref(),
                Obj::Atom(AtomObj::Exist(param)) if param.name.as_str() == numerator_name.as_str()
            ) && matches!(
                div.right.as_ref(),
                Obj::Atom(AtomObj::Exist(param)) if param.name.as_str() == denominator_name.as_str()
            )
        }
        _ => false,
    };

    let other = if is_selected_ratio(&equal_fact.left) {
        &equal_fact.right
    } else if is_selected_ratio(&equal_fact.right) {
        &equal_fact.left
    } else {
        return None;
    };
    if Runtime::obj_depends_on_given_exist_param(
        other,
        &[numerator_name.clone(), denominator_name.clone()],
    ) {
        return None;
    }
    Some(other)
}

fn rational_positive_denominator_exist_fact_non_witness_operand(
    exist_fact: &ExistFactEnum,
) -> Option<&Obj> {
    if !exist_fact.is_plain_exist() || exist_fact.facts().len() != 2 {
        return None;
    }
    let params = exist_fact
        .params_def_with_type()
        .collect_param_names_with_types();
    let [(numerator_name, ParamType::Obj(Obj::StandardSet(StandardSet::Z))), (denominator_name, ParamType::Obj(Obj::StandardSet(StandardSet::Z)))] =
        params.as_slice()
    else {
        return None;
    };

    let is_numerator = |obj: &Obj| matches!(obj, Obj::Atom(AtomObj::Exist(param)) if param.name == *numerator_name);
    let is_denominator = |obj: &Obj| matches!(obj, Obj::Atom(AtomObj::Exist(param)) if param.name == *denominator_name);
    let is_zero = |obj: &Obj| matches!(obj, Obj::Number(number) if number.normalized_value == "0");
    let denominator_is_positive = exist_fact.facts().iter().any(|fact| match fact {
        ExistBodyFact::AtomicFact(AtomicFact::GreaterFact(fact)) => {
            is_denominator(&fact.left) && is_zero(&fact.right)
        }
        ExistBodyFact::AtomicFact(AtomicFact::LessFact(fact)) => {
            is_zero(&fact.left) && is_denominator(&fact.right)
        }
        _ => false,
    });
    if !denominator_is_positive {
        return None;
    }

    let ratio_other = exist_fact.facts().iter().find_map(|fact| {
        let ExistBodyFact::AtomicFact(AtomicFact::EqualFact(equal_fact)) = fact else {
            return None;
        };
        let is_selected_ratio = |obj: &Obj| match obj {
            Obj::Div(div) => is_numerator(div.left.as_ref()) && is_denominator(div.right.as_ref()),
            _ => false,
        };
        if is_selected_ratio(&equal_fact.left) {
            Some(&equal_fact.right)
        } else if is_selected_ratio(&equal_fact.right) {
            Some(&equal_fact.left)
        } else {
            None
        }
    })?;
    if Runtime::obj_depends_on_given_exist_param(
        ratio_other,
        &[numerator_name.clone(), denominator_name.clone()],
    ) {
        return None;
    }
    Some(ratio_other)
}

fn euclidean_quotient_exist_unique_operands(exist_fact: &ExistFactEnum) -> Option<(Obj, Obj)> {
    if !exist_fact.is_exist_unique() || exist_fact.facts().len() != 1 {
        return None;
    }

    let params = exist_fact
        .params_def_with_type()
        .collect_param_names_with_types();
    let [(witness_name, ParamType::Obj(Obj::StandardSet(StandardSet::Z)))] = params.as_slice()
    else {
        return None;
    };
    let ExistBodyFact::AtomicFact(AtomicFact::EqualFact(equal_fact)) = &exist_fact.facts()[0]
    else {
        return None;
    };

    let Obj::Add(decomposition) = &equal_fact.right else {
        return None;
    };
    let Obj::Mul(product) = decomposition.left.as_ref() else {
        return None;
    };
    if !matches!(
        product.right.as_ref(),
        Obj::Atom(AtomObj::Exist(param)) if param.name == *witness_name
    ) {
        return None;
    }
    let Obj::Mod(remainder) = decomposition.right.as_ref() else {
        return None;
    };

    let dividend = equal_fact.left.clone();
    let divisor = product.left.as_ref().clone();
    if dividend.to_string() != remainder.left.to_string()
        || divisor.to_string() != remainder.right.to_string()
        || Runtime::obj_depends_on_given_exist_param(&dividend, &[witness_name.clone()])
        || Runtime::obj_depends_on_given_exist_param(&divisor, &[witness_name.clone()])
    {
        return None;
    }

    Some((dividend, divisor))
}

fn integer_divisibility_exist_fact_operands(exist_fact: &ExistFactEnum) -> Option<(Obj, Obj)> {
    if !exist_fact.is_plain_exist() || exist_fact.facts().len() != 1 {
        return None;
    }
    let params = exist_fact
        .params_def_with_type()
        .collect_param_names_with_types();
    let [(witness_name, ParamType::Obj(Obj::StandardSet(StandardSet::Z)))] = params.as_slice()
    else {
        return None;
    };
    let ExistBodyFact::AtomicFact(AtomicFact::EqualFact(equal_fact)) = &exist_fact.facts()[0]
    else {
        return None;
    };

    let extract_divisor = |candidate: &Obj| match candidate {
        Obj::Mul(product) if matches!(product.left.as_ref(), Obj::Atom(AtomObj::Exist(param)) if param.name == *witness_name) => {
            Some(product.right.as_ref().clone())
        }
        Obj::Mul(product) if matches!(product.right.as_ref(), Obj::Atom(AtomObj::Exist(param)) if param.name == *witness_name) => {
            Some(product.left.as_ref().clone())
        }
        _ => None,
    };

    let (dividend, divisor) = if let Some(divisor) = extract_divisor(&equal_fact.right) {
        (equal_fact.left.clone(), divisor)
    } else if let Some(divisor) = extract_divisor(&equal_fact.left) {
        (equal_fact.right.clone(), divisor)
    } else {
        return None;
    };
    if Runtime::obj_depends_on_given_exist_param(&dividend, &[witness_name.clone()])
        || Runtime::obj_depends_on_given_exist_param(&divisor, &[witness_name.clone()])
    {
        return None;
    }
    Some((dividend, divisor))
}

fn archimedean_reciprocal_bound_non_witness_operand(exist_fact: &ExistFactEnum) -> Option<&Obj> {
    if !exist_fact.is_plain_exist() || exist_fact.facts().len() != 1 {
        return None;
    }
    let params = exist_fact
        .params_def_with_type()
        .collect_param_names_with_types();
    let [(witness_name, ParamType::Obj(Obj::StandardSet(StandardSet::NPos)))] = params.as_slice()
    else {
        return None;
    };
    let ExistBodyFact::AtomicFact(AtomicFact::LessFact(less_fact)) = &exist_fact.facts()[0] else {
        return None;
    };
    let Obj::Div(div) = &less_fact.left else {
        return None;
    };
    if !matches!(div.left.as_ref(), Obj::Number(number) if number.normalized_value == "1")
        || !matches!(div.right.as_ref(), Obj::Atom(AtomObj::Exist(param)) if param.name == *witness_name)
        || Runtime::obj_depends_on_given_exist_param(&less_fact.right, &[witness_name.clone()])
    {
        return None;
    }
    Some(&less_fact.right)
}

fn dense_order_exist_fact_endpoints(
    exist_fact: &ExistFactEnum,
    witness_carrier: StandardSet,
) -> Option<(Obj, Obj)> {
    if !exist_fact.is_plain_exist() || exist_fact.facts().len() != 1 {
        return None;
    }

    let params = exist_fact
        .params_def_with_type()
        .collect_param_names_with_types();
    let [(witness_name, ParamType::Obj(Obj::StandardSet(carrier)))] = params.as_slice() else {
        return None;
    };
    let carrier_matches = matches!(
        (carrier, witness_carrier),
        (StandardSet::Q, StandardSet::Q) | (StandardSet::R, StandardSet::R)
    );
    if !carrier_matches {
        return None;
    }

    let ExistBodyFact::ChainFact(chain) = &exist_fact.facts()[0] else {
        return None;
    };
    let chain_facts = chain.facts().ok()?;
    let [AtomicFact::LessFact(left_less), AtomicFact::LessFact(right_less)] =
        chain_facts.as_slice()
    else {
        return None;
    };

    let is_witness =
        |obj: &Obj| matches!(obj, Obj::Atom(AtomObj::Exist(param)) if param.name == *witness_name);
    if !is_witness(&left_less.right) || !is_witness(&right_less.left) {
        return None;
    }
    if Runtime::obj_depends_on_given_exist_param(&left_less.left, &[witness_name.clone()])
        || Runtime::obj_depends_on_given_exist_param(&right_less.right, &[witness_name.clone()])
    {
        return None;
    }

    Some((left_less.left.clone(), right_less.right.clone()))
}

fn integer_interval_exist_fact_endpoints(exist_fact: &ExistFactEnum) -> Option<(Obj, Obj, bool)> {
    if !exist_fact.is_plain_exist() || exist_fact.facts().len() != 1 {
        return None;
    }

    let params = exist_fact
        .params_def_with_type()
        .collect_param_names_with_types();
    let [(witness_name, ParamType::Obj(Obj::StandardSet(StandardSet::Z)))] = params.as_slice()
    else {
        return None;
    };

    let ExistBodyFact::ChainFact(chain) = &exist_fact.facts()[0] else {
        return None;
    };
    let chain_facts = chain.facts().ok()?;
    let [left_bound, right_bound] = chain_facts.as_slice() else {
        return None;
    };

    let is_witness =
        |obj: &Obj| matches!(obj, Obj::Atom(AtomObj::Exist(param)) if param.name == *witness_name);
    let (left, right, strict) = match (left_bound, right_bound) {
        (AtomicFact::LessFact(left_bound), AtomicFact::LessFact(right_bound))
            if is_witness(&left_bound.right) && is_witness(&right_bound.left) =>
        {
            (&left_bound.left, &right_bound.right, true)
        }
        (AtomicFact::LessEqualFact(left_bound), AtomicFact::LessEqualFact(right_bound))
            if is_witness(&left_bound.right) && is_witness(&right_bound.left) =>
        {
            (&left_bound.left, &right_bound.right, false)
        }
        _ => return None,
    };

    if Runtime::obj_depends_on_given_exist_param(left, &[witness_name.clone()])
        || Runtime::obj_depends_on_given_exist_param(right, &[witness_name.clone()])
    {
        return None;
    }

    Some((left.clone(), right.clone(), strict))
}

fn nonempty_set_exist_fact_set(exist_fact: &ExistFactEnum) -> Option<Obj> {
    if !exist_fact.is_plain_exist() || exist_fact.facts().len() != 1 {
        return None;
    }

    let params = exist_fact
        .params_def_with_type()
        .collect_param_names_with_types();
    let [(witness_name, ParamType::Obj(witness_set))] = params.as_slice() else {
        return None;
    };

    let ExistBodyFact::AtomicFact(AtomicFact::InFact(membership)) = &exist_fact.facts()[0] else {
        return None;
    };
    let witness_is_member = matches!(
        &membership.element,
        Obj::Atom(AtomObj::Exist(param)) if param.name == *witness_name
    );
    if !witness_is_member || membership.set.to_string() != witness_set.to_string() {
        return None;
    }

    Some(witness_set.clone())
}

fn rational_reduced_fraction_exist_fact_non_witness_operand(
    exist_fact: &ExistFactEnum,
) -> Option<Obj> {
    if (!exist_fact.is_plain_exist() && !exist_fact.is_exist_unique())
        || exist_fact.facts().len() != 2
    {
        return None;
    }

    let params = exist_fact
        .params_def_with_type()
        .collect_param_names_with_types();
    let [(numerator_name, ParamType::Obj(Obj::StandardSet(StandardSet::Z))), (denominator_name, ParamType::Obj(Obj::StandardSet(StandardSet::NPos)))] =
        params.as_slice()
    else {
        return None;
    };

    let is_named_exist_param = |obj: &Obj, name: &str| matches!(obj, Obj::Atom(AtomObj::Exist(param)) if param.name == name);
    let is_selected_ratio = |obj: &Obj| match obj {
        Obj::Div(div) => {
            is_named_exist_param(div.left.as_ref(), numerator_name)
                && is_named_exist_param(div.right.as_ref(), denominator_name)
        }
        _ => false,
    };
    let is_zero = |obj: &Obj| matches!(obj, Obj::Number(number) if number.normalized_value == "0");
    let is_one = |obj: &Obj| matches!(obj, Obj::Number(number) if number.normalized_value == "1");

    let rational = exist_fact.facts().iter().find_map(|fact| {
        let ExistBodyFact::AtomicFact(AtomicFact::EqualFact(equal_fact)) = fact else {
            return None;
        };
        if is_selected_ratio(&equal_fact.left) {
            Some(equal_fact.right.clone())
        } else if is_selected_ratio(&equal_fact.right) {
            Some(equal_fact.left.clone())
        } else {
            None
        }
    })?;
    if Runtime::obj_depends_on_given_exist_param(
        &rational,
        &[numerator_name.clone(), denominator_name.clone()],
    ) {
        return None;
    }

    let reducedness_forall = exist_fact.facts().iter().find_map(|fact| match fact {
        ExistBodyFact::InlineForall(forall_fact) => Some(forall_fact),
        _ => None,
    })?;
    let common_divisor_params = reducedness_forall
        .params_def_with_type
        .collect_param_names_with_types();
    let [(common_divisor_name, ParamType::Obj(Obj::StandardSet(StandardSet::NPos)))] =
        common_divisor_params.as_slice()
    else {
        return None;
    };

    let mut divisibility_premises = Vec::new();
    for domain_fact in reducedness_forall.dom_facts.iter() {
        match domain_fact {
            Fact::AtomicFact(atomic_fact) => divisibility_premises.push(atomic_fact),
            Fact::AndFact(and_fact) => divisibility_premises.extend(and_fact.facts.iter()),
            _ => return None,
        }
    }
    if divisibility_premises.len() != 2 || reducedness_forall.then_facts.len() != 1 {
        return None;
    }

    let divides_witness = |atomic_fact: &AtomicFact, dividend_name: &str| {
        let AtomicFact::EqualFact(equal_fact) = atomic_fact else {
            return false;
        };
        let is_remainder = |obj: &Obj| match obj {
            Obj::Mod(modulo) => {
                is_named_exist_param(modulo.left.as_ref(), dividend_name)
                    && matches!(
                        modulo.right.as_ref(),
                        Obj::Atom(AtomObj::Forall(param)) if param.name == *common_divisor_name
                    )
            }
            _ => false,
        };
        (is_remainder(&equal_fact.left) && is_zero(&equal_fact.right))
            || (is_zero(&equal_fact.left) && is_remainder(&equal_fact.right))
    };
    let numerator_divisible = divisibility_premises
        .iter()
        .any(|premise| divides_witness(premise, numerator_name));
    let denominator_divisible = divisibility_premises
        .iter()
        .any(|premise| divides_witness(premise, denominator_name));
    if !numerator_divisible || !denominator_divisible {
        return None;
    }

    let ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(conclusion)) =
        &reducedness_forall.then_facts[0]
    else {
        return None;
    };
    let common_divisor_is_one = |left: &Obj, right: &Obj| {
        matches!(left, Obj::Atom(AtomObj::Forall(param)) if param.name == *common_divisor_name)
            && is_one(right)
    };
    if !common_divisor_is_one(&conclusion.left, &conclusion.right)
        && !common_divisor_is_one(&conclusion.right, &conclusion.left)
    {
        return None;
    }

    Some(rational)
}

impl Runtime {
    pub fn verify_exist_fact(
        &mut self,
        exist_fact: &ExistFactEnum,
        verify_state: &UseContextVerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        if let Some(cached_result) =
            self.verify_fact_from_cache_using_display_string(&exist_fact.clone().into())
        {
            return Ok(cached_result);
        }

        if !verify_state.well_defined_already_verified {
            if let Err(e) = self.verify_exist_fact_well_defined(exist_fact, verify_state) {
                return Err({
                    VerifyRuntimeError(RuntimeErrorStruct::new(
                        Some(Fact::from(exist_fact.clone()).into_stmt()),
                        String::new(),
                        exist_fact.line_file(),
                        Some(e),
                        vec![],
                    ))
                    .into()
                });
            }
        }

        // The real line has witnesses above, below, equal to, and distinct from every real.
        // Example: `have x R:` followed by `x > 100`.
        if let Some(non_witness_operands) =
            real_line_comparison_exist_fact_non_witness_operands(exist_fact)
        {
            if let Some(steps) = self.verify_objects_are_known_reals(
                non_witness_operands.as_slice(),
                &exist_fact.line_file(),
                verify_state,
            )? {
                return Ok(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        exist_fact.clone().into(),
                        "exist: real-line comparison witness".to_string(),
                        steps,
                    )
                    .into(),
                );
            }
        }

        // A nonempty set has a member. This proves only the existential fact,
        // without selecting a global choice object. Example:
        // `$is_nonempty_set(A)` => `exist x A st {x $in A}`.
        if let Some(set) = nonempty_set_exist_fact_set(exist_fact) {
            let nonempty: AtomicFact = IsNonemptySetFact::new(set, exist_fact.line_file()).into();
            let nonempty_result =
                self.verify_non_equational_known_then_builtin_rules_only(&nonempty, verify_state)?;
            if nonempty_result.is_true() {
                return Ok(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        exist_fact.clone().into(),
                        "exist: member of a nonempty set".to_string(),
                        vec![nonempty_result],
                    )
                    .into(),
                );
            }
        }

        // Every rational has one unique reduced integer fraction with a positive
        // denominator. Example: `exist! p Z, q N+ st {a = p / q, forall z
        // N+: p % z = 0 and q % z = 0 => {z = 1}}` for `a Q`.
        if let Some(rational) = rational_reduced_fraction_exist_fact_non_witness_operand(exist_fact)
        {
            let in_q: AtomicFact =
                InFact::new(rational, StandardSet::Q.into(), exist_fact.line_file()).into();
            let rational_membership =
                self.verify_non_equational_known_then_builtin_rules_only(&in_q, verify_state)?;
            if rational_membership.is_true() {
                return Ok(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        exist_fact.clone().into(),
                        if exist_fact.is_exist_unique() {
                            "exist!: unique rational reduced fraction with positive denominator"
                                .to_string()
                        } else {
                            "exist: rational reduced fraction with positive denominator".to_string()
                        },
                        vec![rational_membership],
                    )
                    .into(),
                );
            }
        }

        // Every rational has an integer fraction form with a positive denominator.
        // Example: `exist a, b Z st {b > 0, q = a / b}` for `q Q`.
        if let Some(rational) =
            rational_positive_denominator_exist_fact_non_witness_operand(exist_fact)
        {
            let in_q: AtomicFact = InFact::new(
                rational.clone(),
                StandardSet::Q.into(),
                exist_fact.line_file(),
            )
            .into();
            let rational_membership =
                self.verify_non_equational_known_then_builtin_rules_only(&in_q, verify_state)?;
            if rational_membership.is_true() {
                return Ok(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        exist_fact.clone().into(),
                        "exist: rational representation with positive integer denominator"
                            .to_string(),
                        vec![rational_membership],
                    )
                    .into(),
                );
            }
        }

        // Every rational is represented by an integer numerator and a nonzero
        // integer denominator. Example: `exist a Z, b Z* st {q = a / b}`
        // for `q Q`.
        if let Some(rational) = rational_integer_ratio_exist_fact_non_witness_operand(exist_fact) {
            let in_q: AtomicFact = InFact::new(
                rational.clone(),
                StandardSet::Q.into(),
                exist_fact.line_file(),
            )
            .into();
            let rational_membership =
                self.verify_non_equational_known_then_builtin_rules_only(&in_q, verify_state)?;
            if rational_membership.is_true() {
                return Ok(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        exist_fact.clone().into(),
                        "exist: rational integer ratio representation".to_string(),
                        vec![rational_membership],
                    )
                    .into(),
                );
            }
        }

        // Euclidean division by a positive integer determines a unique integer quotient.
        // Example: a Z, d N+ => exist! q Z st {a = d * q + a % d}.
        if let Some((dividend, divisor)) = euclidean_quotient_exist_unique_operands(exist_fact) {
            let dividend_in_z: AtomicFact =
                InFact::new(dividend, StandardSet::Z.into(), exist_fact.line_file()).into();
            let divisor_in_n_pos: AtomicFact =
                InFact::new(divisor, StandardSet::NPos.into(), exist_fact.line_file()).into();
            let dividend_result = self.verify_non_equational_known_then_builtin_rules_only(
                &dividend_in_z,
                verify_state,
            )?;
            let divisor_result = self.verify_non_equational_known_then_builtin_rules_only(
                &divisor_in_n_pos,
                verify_state,
            )?;
            if dividend_result.is_true() && divisor_result.is_true() {
                return Ok(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        exist_fact.clone().into(),
                        "exist!: unique Euclidean quotient for an integer and positive divisor"
                            .to_string(),
                        vec![dividend_result, divisor_result],
                    )
                    .into(),
                );
            }
        }

        // A zero Euclidean remainder means a nonzero integer modulus divides the integer.
        // Example: `a % b = 0`, `b != 0` => `exist k Z st {a = b * k}`.
        if let Some((dividend, divisor)) = integer_divisibility_exist_fact_operands(exist_fact) {
            let dividend_in_z: AtomicFact = InFact::new(
                dividend.clone(),
                StandardSet::Z.into(),
                exist_fact.line_file(),
            )
            .into();
            let divisor_in_z: AtomicFact = InFact::new(
                divisor.clone(),
                StandardSet::Z.into(),
                exist_fact.line_file(),
            )
            .into();
            let divisor_nonzero: AtomicFact = NotEqualFact::new(
                divisor.clone(),
                Number::new("0".to_string()).into(),
                exist_fact.line_file(),
            )
            .into();
            let zero_remainder: AtomicFact = EqualFact::new(
                Mod::new(dividend, divisor).into(),
                Number::new("0".to_string()).into(),
                exist_fact.line_file(),
            )
            .into();
            let dividend_result = self
                .verify_atomic_fact_by_known_atomic_or_builtin_only(&dividend_in_z, verify_state)?;
            let divisor_result = self
                .verify_atomic_fact_by_known_atomic_or_builtin_only(&divisor_in_z, verify_state)?;
            let divisor_nonzero_result = self.verify_atomic_fact_by_known_atomic_or_builtin_only(
                &divisor_nonzero,
                verify_state,
            )?;
            let remainder_result = self.verify_atomic_fact_by_known_atomic_or_builtin_only(
                &zero_remainder,
                verify_state,
            )?;
            if dividend_result.is_true()
                && divisor_result.is_true()
                && divisor_nonzero_result.is_true()
                && remainder_result.is_true()
            {
                return Ok(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        exist_fact.clone().into(),
                        "exist: zero remainder gives an integer multiple of a nonzero modulus"
                            .to_string(),
                        vec![
                            dividend_result,
                            divisor_result,
                            divisor_nonzero_result,
                            remainder_result,
                        ],
                    )
                    .into(),
                );
            }
        }

        // Every positive real has a reciprocal positive-natural bound.
        // Example: `exist n N+ st {1 / n < epsilon}` for `epsilon $in R+`.
        if let Some(bound) = archimedean_reciprocal_bound_non_witness_operand(exist_fact) {
            let positive_bound: AtomicFact = InFact::new(
                bound.clone(),
                StandardSet::RPos.into(),
                exist_fact.line_file(),
            )
            .into();
            let positive_bound_result = self.verify_non_equational_known_then_builtin_rules_only(
                &positive_bound,
                verify_state,
            )?;
            if positive_bound_result.is_true() {
                return Ok(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        exist_fact.clone().into(),
                        "exist: Archimedean reciprocal bound".to_string(),
                        vec![positive_bound_result],
                    )
                    .into(),
                );
            }
        }

        // Rational density: every nonempty real interval contains a rational.
        // Example: `a < b` => `exist q Q st {a < q < b}`.
        if let Some((left, right)) = dense_order_exist_fact_endpoints(exist_fact, StandardSet::Q) {
            if let Some(mut steps) = self.verify_objects_are_known_reals(
                &[&left, &right],
                &exist_fact.line_file(),
                verify_state,
            )? {
                let interval_nonempty: AtomicFact =
                    LessFact::new(left, right, exist_fact.line_file()).into();
                let interval_result = self.verify_non_equational_known_then_builtin_rules_only(
                    &interval_nonempty,
                    verify_state,
                )?;
                if interval_result.is_true() {
                    steps.push(interval_result);
                    return Ok(
                        FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                            exist_fact.clone().into(),
                            "exist: rational density in the real line".to_string(),
                            steps,
                        )
                        .into(),
                    );
                }
            }
        }

        // Real density: the midpoint of two ordered reals lies strictly between them.
        // Example: `a < b` => `exist r R st {a < r < b}`.
        if let Some((left, right)) = dense_order_exist_fact_endpoints(exist_fact, StandardSet::R) {
            if let Some(mut steps) = self.verify_objects_are_known_reals(
                &[&left, &right],
                &exist_fact.line_file(),
                verify_state,
            )? {
                let interval_nonempty: AtomicFact =
                    LessFact::new(left, right, exist_fact.line_file()).into();
                let interval_result = self.verify_non_equational_known_then_builtin_rules_only(
                    &interval_nonempty,
                    verify_state,
                )?;
                if interval_result.is_true() {
                    steps.push(interval_result);
                    return Ok(
                        FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                            exist_fact.clone().into(),
                            "exist: real density by the midpoint principle".to_string(),
                            steps,
                        )
                        .into(),
                    );
                }
            }
        }

        // An interval of real length greater than one has a strict integer witness; length at
        // least one has a closed integer witness. These can also be proved by induction on an
        // integer interval, but are builtin bridges for routine interval arithmetic.
        // Examples: `b - a > 1 => exist c Z st {a < c < b}` and
        // `b - a >= 1 => exist c Z st {a <= c <= b}`.
        if let Some((left, right, strict)) = integer_interval_exist_fact_endpoints(exist_fact) {
            if let Some(mut steps) = self.verify_objects_are_known_reals(
                &[&left, &right],
                &exist_fact.line_file(),
                verify_state,
            )? {
                let one: Obj = Number::new("1".to_string()).into();
                let gap = Sub::new(right.clone(), left.clone()).into();
                let gap_requirement: AtomicFact = if strict {
                    GreaterFact::new(gap, one, exist_fact.line_file()).into()
                } else {
                    GreaterEqualFact::new(gap, one, exist_fact.line_file()).into()
                };
                let gap_result = self.verify_non_equational_known_then_builtin_rules_only(
                    &gap_requirement,
                    verify_state,
                )?;
                if gap_result.is_true() {
                    steps.push(gap_result);
                    let rule = if strict {
                        "exist: integer strictly inside a real interval wider than 1"
                    } else {
                        "exist: integer inside a real interval of length at least 1"
                    };
                    return Ok(
                        FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                            exist_fact.clone().into(),
                            rule.to_string(),
                            steps,
                        )
                        .into(),
                    );
                }
            }
        }

        let result = self.verify_exist_fact_with_known_exist_fact(exist_fact, exist_fact)?;
        if result.is_true() {
            return Ok(result);
        }

        if verify_state.is_round_0() {
            let result = self.verify_exist_fact_with_known_forall(exist_fact, verify_state)?;
            if result.is_true() {
                return Ok(result);
            }

            if exist_fact.is_exist_unique() {
                if let Some(proved) = self.try_verify_exist_unique_by_exist_and_uniqueness_forall(
                    exist_fact,
                    verify_state,
                )? {
                    return Ok(proved);
                }
            }
        }

        // A finite nonempty subset of N has a greatest element. Keep this bounded fallback after
        // the established existential strategies so inspecting an unrelated existential cannot
        // perturb their inference order. The rule accepts a user proposition whose concrete
        // definition is exactly membership plus the universal upper-bound property.
        if let Some(result) =
            self.verify_finite_nonempty_natural_set_has_maximum(exist_fact, verify_state)?
        {
            return Ok(result);
        }

        Ok(StmtUnknown::new().into())
    }

    fn verify_finite_nonempty_natural_set_has_maximum(
        &mut self,
        exist_fact: &ExistFactEnum,
        verify_state: &UseContextVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let ExistFactEnum::ExistFact(body) = exist_fact else {
            return Ok(None);
        };
        let groups = &body.params_def_with_type.groups;
        if groups.len() != 1 || groups[0].params.len() != 1 {
            return Ok(None);
        }
        let ParamType::Obj(witness_carrier) = &groups[0].param_type else {
            return Ok(None);
        };
        if witness_carrier.to_string() != StandardSet::N.to_string() {
            return Ok(None);
        }
        let witness = obj_for_bound_param_in_scope(&groups[0].params[0], ParamObjType::Exist);
        let [ExistBodyFact::AtomicFact(AtomicFact::NormalAtomicFact(maximum_prop))] =
            body.facts.as_slice()
        else {
            return Ok(None);
        };
        let Some(definition) =
            self.get_active_prop_definition_by_name(&maximum_prop.predicate.to_string())
        else {
            return Ok(None);
        };
        if definition.iff_facts.len() != 2 {
            return Ok(None);
        }
        let param_to_arg_map = definition
            .params_def_with_type
            .param_defs_and_args_to_param_to_arg_map(maximum_prop.body.as_slice());
        let member_clause = self.inst_fact(
            &definition.iff_facts[0],
            &param_to_arg_map,
            ParamObjType::DefHeader,
            None,
        )?;
        let upper_bound_clause = self.inst_fact(
            &definition.iff_facts[1],
            &param_to_arg_map,
            ParamObjType::DefHeader,
            None,
        )?;
        let Fact::AtomicFact(AtomicFact::InFact(member)) = member_clause else {
            return Ok(None);
        };
        if member.element.to_string() != witness.to_string() {
            return Ok(None);
        }
        let Fact::ForallFact(upper_bound) = upper_bound_clause else {
            return Ok(None);
        };
        let upper_groups = &upper_bound.params_def_with_type.groups;
        if upper_groups.len() != 1 || upper_groups[0].params.len() != 1 {
            return Ok(None);
        }
        let ParamType::Obj(upper_carrier) = &upper_groups[0].param_type else {
            return Ok(None);
        };
        if upper_carrier.to_string() != StandardSet::N.to_string()
            || upper_bound.dom_facts.len() != 1
            || upper_bound.then_facts.len() != 1
        {
            return Ok(None);
        }
        let Fact::AtomicFact(AtomicFact::InFact(domain_member)) = &upper_bound.dom_facts[0] else {
            return Ok(None);
        };
        let ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::LessEqualFact(bound)) =
            &upper_bound.then_facts[0]
        else {
            return Ok(None);
        };
        let upper_param =
            obj_for_bound_param_in_scope(&upper_groups[0].params[0], ParamObjType::Forall);
        if domain_member.element.to_string() != upper_param.to_string()
            || domain_member.set.to_string() != member.set.to_string()
            || bound.left.to_string() != upper_param.to_string()
            || bound.right.to_string() != witness.to_string()
        {
            return Ok(None);
        }

        let line_file = exist_fact.line_file();
        let prerequisites = [
            AtomicFact::from(IsFiniteSetFact::new(member.set.clone(), line_file.clone())),
            AtomicFact::from(IsNonemptySetFact::new(
                member.set.clone(),
                line_file.clone(),
            )),
            AtomicFact::from(SubsetFact::new(
                member.set.clone(),
                StandardSet::N.into(),
                line_file,
            )),
        ];
        let mut steps = Vec::with_capacity(prerequisites.len());
        for prerequisite in prerequisites {
            let result = self
                .verify_non_equational_known_then_builtin_rules_only(&prerequisite, verify_state)?;
            if !result.is_true() {
                return Ok(None);
            }
            steps.push(result);
        }

        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                exist_fact.clone().into(),
                "finite nonempty natural set has a greatest member".to_string(),
                steps,
            )
            .into(),
        ))
    }

    pub(crate) fn build_exist_unique_uniqueness_forall_fact(
        &self,
        exist_fact: &ExistFactEnum,
    ) -> Result<ForallFact, RuntimeError> {
        self.build_exist_unique_uniqueness_forall_fact_inner(exist_fact, false)
    }

    pub(crate) fn build_exist_unique_component_uniqueness_forall_fact(
        &self,
        exist_fact: &ExistFactEnum,
    ) -> Result<ForallFact, RuntimeError> {
        self.build_exist_unique_uniqueness_forall_fact_inner(exist_fact, true)
    }

    fn build_exist_unique_uniqueness_forall_fact_inner(
        &self,
        exist_fact: &ExistFactEnum,
        component_conclusion: bool,
    ) -> Result<ForallFact, RuntimeError> {
        let lf = exist_fact.line_file();
        let flat_orig = exist_fact.params_def_with_type().collect_param_bindings();
        let n = flat_orig.len();
        let mut reserved_names = HashSet::new();
        self.collect_param_obj_names_in_exist_fact(
            exist_fact,
            ParamObjType::Forall,
            &mut reserved_names,
        );
        let mut flat_a = Vec::with_capacity(n);
        let mut flat_b = Vec::with_capacity(n);
        for _ in &flat_orig {
            let name = self.generate_one_unused_name_with_reserved(&reserved_names);
            reserved_names.insert(name.clone());
            flat_a.push(self.allocate_local_symbol_binding(name)?);
        }
        for _ in &flat_orig {
            let name = self.generate_one_unused_name_with_reserved(&reserved_names);
            reserved_names.insert(name.clone());
            flat_b.push(self.allocate_local_symbol_binding(name)?);
        }

        let mut map_running_a: HashMap<String, Obj> = HashMap::new();
        let mut map_running_b: HashMap<String, Obj> = HashMap::new();
        let mut forall_groups: Vec<ParamGroupWithParamType> = Vec::new();
        for group in exist_fact.params_def_with_type().groups.iter() {
            let chunk_a: Vec<SymbolBinding> = group
                .params
                .iter()
                .map(|binding| {
                    let index = flat_orig
                        .iter()
                        .position(|original| original.id() == binding.id())
                        .expect("exist uniqueness binder must be in flattened parameter list");
                    flat_a[index].clone()
                })
                .collect();
            let pt_a = self.inst_param_type(
                &group.param_type,
                &map_running_a,
                ParamObjType::BinderRetag(BinderRetagSource::Exist),
            )?;
            for (orig, target) in group.params.iter().zip(chunk_a.iter()) {
                insert_symbol_substitution(
                    &mut map_running_a,
                    orig,
                    obj_for_bound_param_in_scope(target, ParamObjType::Forall),
                );
            }
            forall_groups.push(ParamGroupWithParamType::new(chunk_a, pt_a));
        }
        for group in exist_fact.params_def_with_type().groups.iter() {
            let chunk_b: Vec<SymbolBinding> = group
                .params
                .iter()
                .map(|binding| {
                    let index = flat_orig
                        .iter()
                        .position(|original| original.id() == binding.id())
                        .expect("exist uniqueness binder must be in flattened parameter list");
                    flat_b[index].clone()
                })
                .collect();
            let pt_b = self.inst_param_type(
                &group.param_type,
                &map_running_b,
                ParamObjType::BinderRetag(BinderRetagSource::Exist),
            )?;
            for (orig, target) in group.params.iter().zip(chunk_b.iter()) {
                insert_symbol_substitution(
                    &mut map_running_b,
                    orig,
                    obj_for_bound_param_in_scope(target, ParamObjType::Forall),
                );
            }
            forall_groups.push(ParamGroupWithParamType::new(chunk_b, pt_b));
        }

        let mut map_a = HashMap::new();
        let mut map_b = HashMap::new();
        for ((source, target_a), target_b) in flat_orig.iter().zip(&flat_a).zip(&flat_b) {
            insert_symbol_substitution(
                &mut map_a,
                source,
                obj_for_bound_param_in_scope(target_a, ParamObjType::Forall),
            );
            insert_symbol_substitution(
                &mut map_b,
                source,
                obj_for_bound_param_in_scope(target_b, ParamObjType::Forall),
            );
        }

        // Retag only existential witness atoms into the two forall copies. Concrete identifiers
        // with the same spelling are captured from the surrounding environment and stay rigid.
        let mut dom_facts: Vec<Fact> = Vec::new();
        for inner in exist_fact.facts().iter() {
            let f_a = self.inst_exist_body_fact(
                inner,
                &map_a,
                ParamObjType::BinderRetag(BinderRetagSource::Exist),
                None,
            )?;
            dom_facts.push(f_a.to_fact());
        }
        for inner in exist_fact.facts().iter() {
            let f_b = self.inst_exist_body_fact(
                inner,
                &map_b,
                ParamObjType::BinderRetag(BinderRetagSource::Exist),
                None,
            )?;
            dom_facts.push(f_b.to_fact());
        }

        let mut then_facts: Vec<ExistOrAndChainAtomicFact> = Vec::new();
        if n == 1 {
            let eq = EqualFact::new(
                obj_for_bound_param_in_scope(&flat_a[0], ParamObjType::Forall),
                obj_for_bound_param_in_scope(&flat_b[0], ParamObjType::Forall),
                lf.clone(),
            );
            then_facts.push(ExistOrAndChainAtomicFact::AtomicFact(eq.into()));
        } else if component_conclusion {
            let mut equal_facts: Vec<AtomicFact> = Vec::new();
            for (left, right) in flat_a.iter().zip(flat_b.iter()) {
                equal_facts.push(
                    EqualFact::new(
                        obj_for_bound_param_in_scope(left, ParamObjType::Forall),
                        obj_for_bound_param_in_scope(right, ParamObjType::Forall),
                        lf.clone(),
                    )
                    .into(),
                );
            }
            then_facts.push(AndFact::new(equal_facts, lf.clone()).into());
        } else {
            let left_tuple: Obj = Tuple::new(
                flat_a
                    .iter()
                    .map(|binding| obj_for_bound_param_in_scope(binding, ParamObjType::Forall))
                    .collect::<Vec<Obj>>(),
            )
            .into();
            let right_tuple: Obj = Tuple::new(
                flat_b
                    .iter()
                    .map(|binding| obj_for_bound_param_in_scope(binding, ParamObjType::Forall))
                    .collect::<Vec<Obj>>(),
            )
            .into();
            let eq = EqualFact::new(left_tuple, right_tuple, lf.clone());
            then_facts.push(ExistOrAndChainAtomicFact::AtomicFact(eq.into()));
        }

        ForallFact::new_canonical_forall(
            ParamDefWithType::new(forall_groups),
            dom_facts,
            then_facts,
            lf,
        )
    }

    fn try_verify_exist_unique_by_exist_and_uniqueness_forall(
        &mut self,
        exist_fact: &ExistFactEnum,
        verify_state: &UseContextVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if exist_fact.params_def_with_type().number_of_params() == 0 {
            return Ok(None);
        }
        let plain = ExistFactEnum::ExistFact(ExistFactBody::new(
            exist_fact.params_def_with_type().clone(),
            exist_fact.facts().clone(),
            exist_fact.line_file(),
        )?);
        let wd_ok = verify_state.with_well_defined_already_verified();
        let plain_res = self.verify_exist_fact(&plain, &wd_ok)?;
        if !plain_res.is_true() {
            return Ok(None);
        }

        let uniqueness_forall = self.build_exist_unique_uniqueness_forall_fact(exist_fact)?;

        let uniqueness_fact: Fact = uniqueness_forall.clone().into();
        let uniq_res = self.verify_fact_full(&uniqueness_fact, &wd_ok)?;
        if !uniq_res.is_true() {
            return Ok(None);
        }

        let mut infers = InferResult::new();
        infers.new_fact(&exist_fact.clone().into());
        infers.new_infer_result_inside(stmt_result_infers(&plain_res));
        infers.new_infer_result_inside(stmt_result_infers(&uniq_res));
        infers.new_fact(&uniqueness_fact);

        let out = FactualStmtSuccess::new_with_verified_by_known_fact_and_infer(
            exist_fact.clone().into(),
            infers,
            VerifiedByResult::cited_fact(
                exist_fact.clone().into(),
                uniqueness_fact.clone(),
                Some("exist!: witness exist and uniqueness forall verified".to_string()),
            ),
            vec![],
        );
        Ok(Some(out.into()))
    }

    pub fn verify_exist_fact_with_known_exist_fact(
        &mut self,
        exist_fact: &ExistFactEnum,
        known_exist_fact: &ExistFactEnum,
    ) -> Result<StmtResult, RuntimeError> {
        for environment in self.iter_environments_from_top() {
            let result = Self::verify_exist_fact_with_known_exist_fact_with_facts_in_environment(
                self,
                environment,
                exist_fact,
                known_exist_fact,
            )?;
            if result.is_true() {
                return Ok(result);
            }
        }

        Ok((StmtUnknown::new()).into())
    }

    pub fn verify_exist_fact_with_known_exist_fact_with_facts_in_environment(
        runtime: &Runtime,
        environment: &Environment,
        exist_fact: &ExistFactEnum,
        known_exist_fact: &ExistFactEnum,
    ) -> Result<StmtResult, RuntimeError> {
        let goal_keys = Self::known_exist_lookup_keys(known_exist_fact);
        let target_body_string = Self::exist_fact_normalized_body_string(runtime, exist_fact)
            .map_err(|e| {
                RuntimeError::from(VerifyRuntimeError(RuntimeErrorStruct::new(
                    Some(Fact::from(exist_fact.clone()).into_stmt()),
                    String::new(),
                    exist_fact.line_file(),
                    Some(e),
                    vec![],
                )))
            })?;
        for key in goal_keys.iter() {
            let Some(known_exist_facts) = environment.known_exist_facts.get(key) else {
                continue;
            };
            for known_fact in known_exist_facts.iter() {
                if !known_fact.can_be_used_to_verify_goal(exist_fact) {
                    continue;
                }
                let known_body_string =
                    Self::exist_fact_normalized_body_string(runtime, known_fact).map_err(|e| {
                        RuntimeError::from(VerifyRuntimeError(RuntimeErrorStruct::new(
                            Some(Fact::from(exist_fact.clone()).into_stmt()),
                            String::new(),
                            exist_fact.line_file(),
                            Some(e),
                            vec![],
                        )))
                    })?;
                if target_body_string == known_body_string {
                    return Ok((FactualStmtSuccess::new_with_verified_by_known_fact(
                        exist_fact.clone().into(),
                        VerifiedByResult::cited_fact(
                            exist_fact.clone().into(),
                            known_fact.clone().into(),
                            None,
                        ),
                        Vec::new(),
                    ))
                    .into());
                }
            }
        }

        Ok((StmtUnknown::new()).into())
    }

    fn known_exist_lookup_keys(goal: &ExistFactEnum) -> Vec<String> {
        let mut keys = vec![goal.alpha_normalized_key(), goal.key()];
        if let ExistFactEnum::ExistFact(body) = goal {
            let unique = ExistFactEnum::ExistUniqueFact(body.clone());
            keys.push(unique.alpha_normalized_key());
            keys.push(unique.key());
        }
        keys.sort();
        keys.dedup();
        keys
    }

    pub(crate) fn exist_fact_normalized_body_string(
        runtime: &Runtime,
        exist_fact: &ExistFactEnum,
    ) -> Result<String, RuntimeError> {
        let mut param_to_arg_map: HashMap<String, Obj> = HashMap::new();
        let mut param_index: usize = 0;

        for param_def_with_type in exist_fact.params_def_with_type().groups.iter() {
            for original_binding in param_def_with_type.params.iter() {
                let normalized_name = format!("#{}", param_index);
                let normalized_binding =
                    SymbolBinding::alpha_canonical(param_index, normalized_name);
                param_index += 1;
                insert_symbol_substitution(
                    &mut param_to_arg_map,
                    original_binding,
                    obj_for_bound_param_in_scope(&normalized_binding, ParamObjType::Exist),
                );
            }
        }

        let instantiated_exist_fact =
            runtime.alpha_rename_exist_fact(exist_fact, &param_to_arg_map)?;

        let mut fact_strings: Vec<String> = Vec::new();
        for fact in instantiated_exist_fact.facts().iter() {
            let fact_as_fact = fact.from_ref_to_cloned_fact();
            match fact_as_fact {
                Fact::ForallFact(forall_fact) => {
                    fact_strings.push(runtime.alpha_normalized_forall_cache_key(&forall_fact)?);
                }
                fact => fact_strings.push(nested_obj_binder_normalized_fact_key(&fact)),
            }
        }

        let mut params_string_parts: Vec<String> = Vec::new();
        for param_def_with_type in instantiated_exist_fact.params_def_with_type().groups.iter() {
            let param_type_string = match &param_def_with_type.param_type {
                ParamType::Obj(obj) => obj_equality_key(obj),
                param_type => param_type.to_string(),
            };
            params_string_parts.push(format!(
                "{} {}",
                vec_to_string_with_sep(&param_def_with_type.params, ",".to_string()),
                param_type_string
            ));
        }
        let params_string = params_string_parts.join("; ");
        let facts_string = fact_strings.join("; ");
        Ok(format!("{} || {}", params_string, facts_string))
    }
}

fn stmt_result_infers(result: &StmtResult) -> InferResult {
    result.infer_result()
}
