use super::*;

impl Runtime {
    // Proves the scalar arithmetic signatures, preserving real specializations while exposing
    // the complex maximum carrier and its natural/integer power domains.
    // Example: `+ $in fn(a, b C) C` and `^ $in fn(z C, n N) C`.
    pub(super) fn maybe_verify_in_fact_builtin_operator_signature(
        &mut self,
        in_fact: &InFact,
    ) -> Option<StmtResult> {
        let (Obj::Atom(AtomObj::Identifier(identifier)), Obj::FnSet(fn_set)) =
            (&in_fact.element, &in_fact.set)
        else {
            return None;
        };

        let is_add_sub_or_mul =
            identifier.is_builtin(ADD) || identifier.is_builtin(SUB) || identifier.is_builtin(MUL);
        let reason = if is_add_sub_or_mul
            && fn_set_has_exact_standard_signature(
                fn_set,
                &[StandardSet::C, StandardSet::C],
                StandardSet::C,
            )
            && fn_set.body.dom_facts.is_empty()
        {
            "complex binary arithmetic operator signature"
        } else if is_add_sub_or_mul
            && fn_set_has_exact_standard_signature(
                fn_set,
                &[StandardSet::R, StandardSet::R],
                StandardSet::R,
            )
            && fn_set.body.dom_facts.is_empty()
        {
            "real binary arithmetic operator signature"
        } else if identifier.is_builtin(DIV)
            && fn_set_has_exact_standard_signature(
                fn_set,
                &[StandardSet::C, StandardSet::C],
                StandardSet::C,
            )
            && fn_set_has_nonzero_second_parameter_condition(fn_set)
        {
            "complex division operator signature"
        } else if identifier.is_builtin(DIV)
            && fn_set_has_exact_standard_signature(
                fn_set,
                &[StandardSet::R, StandardSet::R],
                StandardSet::R,
            )
            && fn_set_has_nonzero_second_parameter_condition(fn_set)
        {
            "real division operator signature"
        } else if identifier.is_builtin(MOD)
            && fn_set_has_exact_standard_signature(
                fn_set,
                &[StandardSet::Z, StandardSet::Z],
                StandardSet::Z,
            )
            && fn_set_has_nonzero_second_parameter_condition(fn_set)
        {
            "integer modulo operator signature"
        } else if identifier.is_builtin(POW)
            && fn_set_has_exact_standard_signature(
                fn_set,
                &[StandardSet::C, StandardSet::N],
                StandardSet::C,
            )
            && fn_set.body.dom_facts.is_empty()
        {
            "complex natural-power operator signature"
        } else if identifier.is_builtin(POW)
            && fn_set_has_exact_standard_signature(
                fn_set,
                &[StandardSet::C, StandardSet::Z],
                StandardSet::C,
            )
            && fn_set_has_nonzero_first_parameter_condition(fn_set)
        {
            "nonzero complex integer-power operator signature"
        } else if identifier.is_builtin(POW)
            && fn_set_has_exact_standard_signature(
                fn_set,
                &[StandardSet::R, StandardSet::R],
                StandardSet::R,
            )
            && fn_set_has_real_power_domain_condition(fn_set)
        {
            "real power operator signature"
        } else {
            return None;
        };

        Some(number_in_set_verified_by_builtin_rules_result(
            in_fact, reason,
        ))
    }
}

fn fn_set_has_exact_standard_signature(
    fn_set: &FnSet,
    param_sets: &[StandardSet],
    ret_set: StandardSet,
) -> bool {
    if !standard_set_obj_matches(fn_set.body.ret_set.as_ref(), ret_set) {
        return false;
    }

    let mut param_index = 0;
    for group in fn_set.body.params_def_with_set.iter() {
        for _ in group.params.iter() {
            let Some(expected_set) = param_sets.get(param_index) else {
                return false;
            };
            if !standard_set_obj_matches(group.set_obj(), expected_set.clone()) {
                return false;
            }
            param_index += 1;
        }
    }
    param_index == param_sets.len()
}

fn standard_set_obj_matches(obj: &Obj, expected_set: StandardSet) -> bool {
    matches!(
        (obj, expected_set),
        (Obj::StandardSet(StandardSet::C), StandardSet::C)
            | (Obj::StandardSet(StandardSet::R), StandardSet::R)
            | (Obj::StandardSet(StandardSet::Q), StandardSet::Q)
            | (Obj::StandardSet(StandardSet::Z), StandardSet::Z)
            | (Obj::StandardSet(StandardSet::N), StandardSet::N)
            | (Obj::StandardSet(StandardSet::RPos), StandardSet::RPos)
            | (Obj::StandardSet(StandardSet::RNz), StandardSet::RNz)
            | (Obj::StandardSet(StandardSet::NPos), StandardSet::NPos)
    )
}

fn fn_set_has_nonzero_second_parameter_condition(fn_set: &FnSet) -> bool {
    let params = fn_set.get_params();
    let Some(second_param) = params.get(1) else {
        return false;
    };
    let [OrAndChainAtomicFact::AtomicFact(AtomicFact::NotEqualFact(not_equal))] =
        fn_set.body.dom_facts.as_slice()
    else {
        return false;
    };
    obj_is_fn_set_param_named(&not_equal.left, second_param)
        && obj_is_literal_zero(&not_equal.right)
}

fn fn_set_has_nonzero_first_parameter_condition(fn_set: &FnSet) -> bool {
    let params = fn_set.get_params();
    let Some(first_param) = params.first() else {
        return false;
    };
    let [OrAndChainAtomicFact::AtomicFact(AtomicFact::NotEqualFact(not_equal))] =
        fn_set.body.dom_facts.as_slice()
    else {
        return false;
    };
    obj_is_fn_set_param_named(&not_equal.left, first_param) && obj_is_literal_zero(&not_equal.right)
}

fn obj_is_fn_set_param_named(obj: &Obj, name: &str) -> bool {
    matches!(obj, Obj::Atom(AtomObj::FnSet(param)) if param.name == name)
}

fn obj_is_literal_zero(obj: &Obj) -> bool {
    matches!(obj, Obj::Number(number) if number.normalized_value == "0")
}

fn fn_set_has_real_power_domain_condition(fn_set: &FnSet) -> bool {
    let params = fn_set.get_params();
    let [base, exponent] = params.as_slice() else {
        return false;
    };
    let [OrAndChainAtomicFact::OrFact(domain_fact)] = fn_set.body.dom_facts.as_slice() else {
        return false;
    };
    let [positive_base, zero_base_positive_exponent, nonzero_integer_exponent, natural_exponent] =
        domain_fact.facts.as_slice()
    else {
        return false;
    };
    let AndChainAtomicFact::AndFact(zero_base_positive_exponent) = zero_base_positive_exponent
    else {
        return false;
    };
    let [zero_base, positive_exponent] = zero_base_positive_exponent.facts.as_slice() else {
        return false;
    };
    let AndChainAtomicFact::AndFact(nonzero_integer_exponent) = nonzero_integer_exponent else {
        return false;
    };
    let [nonzero_base, integer_exponent] = nonzero_integer_exponent.facts.as_slice() else {
        return false;
    };

    and_chain_is_param_in_set(positive_base, base, StandardSet::RPos)
        && atomic_is_param_equal_to_zero(zero_base, base)
        && atomic_is_param_in_set(positive_exponent, exponent, StandardSet::RPos)
        && atomic_is_param_in_set(nonzero_base, base, StandardSet::RNz)
        && atomic_is_param_in_set(integer_exponent, exponent, StandardSet::Z)
        && and_chain_is_param_in_set(natural_exponent, exponent, StandardSet::N)
}

fn and_chain_is_param_in_set(
    fact: &AndChainAtomicFact,
    param_name: &str,
    standard_set: StandardSet,
) -> bool {
    matches!(fact, AndChainAtomicFact::AtomicFact(atomic) if atomic_is_param_in_set(atomic, param_name, standard_set))
}

fn atomic_is_param_in_set(
    atomic: &AtomicFact,
    param_name: &str,
    standard_set: StandardSet,
) -> bool {
    matches!(atomic, AtomicFact::InFact(in_fact) if obj_is_fn_set_param_named(&in_fact.element, param_name) && standard_set_obj_matches(&in_fact.set, standard_set))
}

fn atomic_is_param_equal_to_zero(atomic: &AtomicFact, param_name: &str) -> bool {
    matches!(atomic, AtomicFact::EqualFact(equal) if obj_is_fn_set_param_named(&equal.left, param_name) && obj_is_literal_zero(&equal.right))
}
