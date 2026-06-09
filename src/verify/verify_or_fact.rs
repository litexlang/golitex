use crate::prelude::*;
use crate::verify::verify_equality_by_builtin_rules::objs_equal_by_display_string;
use std::result::Result;

/// Two atomic facts of the form `s > t` / `s <= t` (or `<` / `>=`) with the same left and right
/// operands; the disjunction is a trivial order split (totally ordered carriers such as `R`).
fn order_split_or_is_exhaustive_pair(a: &AtomicFact, b: &AtomicFact) -> bool {
    use AtomicFact::*;
    match (a, b) {
        (GreaterFact(g), LessEqualFact(le)) => {
            objs_equal_by_display_string(&g.left, &le.left)
                && objs_equal_by_display_string(&g.right, &le.right)
        }
        (LessFact(l), GreaterEqualFact(ge)) => {
            objs_equal_by_display_string(&l.left, &ge.left)
                && objs_equal_by_display_string(&l.right, &ge.right)
        }
        (LessEqualFact(le), GreaterFact(g)) => {
            objs_equal_by_display_string(&le.left, &g.left)
                && objs_equal_by_display_string(&le.right, &g.right)
        }
        (GreaterEqualFact(ge), LessFact(l)) => {
            objs_equal_by_display_string(&ge.left, &l.left)
                && objs_equal_by_display_string(&ge.right, &l.right)
        }
        _ => false,
    }
}

fn equality_and_strict_order_need_weak_bound(
    equality: &AtomicFact,
    strict: &AtomicFact,
) -> Option<AtomicFact> {
    let AtomicFact::EqualFact(eq) = equality else {
        return None;
    };
    match strict {
        AtomicFact::GreaterFact(g)
            if (objs_equal_by_display_string(&eq.left, &g.left)
                && objs_equal_by_display_string(&eq.right, &g.right))
                || (objs_equal_by_display_string(&eq.left, &g.right)
                    && objs_equal_by_display_string(&eq.right, &g.left)) =>
        {
            Some(GreaterEqualFact::new(g.left.clone(), g.right.clone(), g.line_file.clone()).into())
        }
        AtomicFact::LessFact(l)
            if (objs_equal_by_display_string(&eq.left, &l.left)
                && objs_equal_by_display_string(&eq.right, &l.right))
                || (objs_equal_by_display_string(&eq.left, &l.right)
                    && objs_equal_by_display_string(&eq.right, &l.left)) =>
        {
            Some(LessEqualFact::new(l.left.clone(), l.right.clone(), l.line_file.clone()).into())
        }
        _ => None,
    }
}

fn obj_is_literal_neg_one_for_abs_or_builtin(obj: &Obj) -> bool {
    match obj {
        Obj::Number(n) => n.normalized_value == "-1",
        _ => false,
    }
}

fn obj_is_negation_of_for_abs_or_builtin(obj: &Obj, expected_arg: &Obj) -> bool {
    match obj {
        Obj::Mul(m) => {
            (obj_is_literal_neg_one_for_abs_or_builtin(m.left.as_ref())
                && objs_equal_by_display_string(m.right.as_ref(), expected_arg))
                || (obj_is_literal_neg_one_for_abs_or_builtin(m.right.as_ref())
                    && objs_equal_by_display_string(m.left.as_ref(), expected_arg))
        }
        _ => false,
    }
}

fn abs_sign_split_or_is_exhaustive_pair(a: &AtomicFact, b: &AtomicFact) -> bool {
    let (AtomicFact::EqualFact(first), AtomicFact::EqualFact(second)) = (a, b) else {
        return false;
    };
    let (arg, first_other) = match (&first.left, &first.right) {
        (Obj::Abs(abs), other) => (abs.arg.as_ref(), other),
        (other, Obj::Abs(abs)) => (abs.arg.as_ref(), other),
        _ => return false,
    };
    if !objs_equal_by_display_string(arg, first_other) {
        return false;
    }
    let (second_arg, second_other) = match (&second.left, &second.right) {
        (Obj::Abs(abs), other) => (abs.arg.as_ref(), other),
        (other, Obj::Abs(abs)) => (abs.arg.as_ref(), other),
        _ => return false,
    };
    objs_equal_by_display_string(arg, second_arg)
        && obj_is_negation_of_for_abs_or_builtin(second_other, arg)
}

fn positive_integer_number_to_usize_for_mod_or_builtin(number: &Number) -> Option<usize> {
    let value = normalized_nonnegative_integer_number_to_usize_for_mod_or_builtin(number)?;
    if value == 0 {
        return None;
    }
    Some(value)
}

fn nonnegative_integer_number_to_usize_for_mod_or_builtin(number: &Number) -> Option<usize> {
    normalized_nonnegative_integer_number_to_usize_for_mod_or_builtin(number)
}

fn normalized_nonnegative_integer_number_to_usize_for_mod_or_builtin(
    number: &Number,
) -> Option<usize> {
    let value = number.normalized_value.trim();
    if value.starts_with('-') {
        return None;
    }
    let unsigned = value.trim_start_matches('+');
    let integer_part = match unsigned.find('.') {
        Some(index) => {
            let fractional_part = &unsigned[index + 1..];
            if !fractional_part.chars().all(|c| c == '0') {
                return None;
            }
            &unsigned[..index]
        }
        None => unsigned,
    };
    integer_part.parse::<usize>().ok()
}

fn mod_obj_and_residue_from_atomic_equal_for_mod_or_builtin(
    atomic_fact: &AtomicFact,
) -> Option<(&Obj, &Number, &Number)> {
    let AtomicFact::EqualFact(eq) = atomic_fact else {
        return None;
    };
    match (&eq.left, &eq.right) {
        (Obj::Mod(m), Obj::Number(residue)) => match m.right.as_ref() {
            Obj::Number(modulus) => Some((m.left.as_ref(), modulus, residue)),
            _ => None,
        },
        (Obj::Number(residue), Obj::Mod(m)) => match m.right.as_ref() {
            Obj::Number(modulus) => Some((m.left.as_ref(), modulus, residue)),
            _ => None,
        },
        _ => None,
    }
}

// Remainder by a positive integer covers exactly one residue class.
// If m > 1, `x % m = 0 or x % m = 1 or ... or x % m = m - 1` is exhaustive.
// Example: `forall x Z: x % 2 = 0 or x % 2 = 1`.
fn mod_positive_integer_residue_or_is_exhaustive(or_fact: &OrFact) -> bool {
    if or_fact.facts.is_empty() {
        return false;
    }

    let first_atomic = match &or_fact.facts[0] {
        AndChainAtomicFact::AtomicFact(atomic) => atomic,
        _ => return false,
    };
    let Some((first_obj, first_modulus, first_residue)) =
        mod_obj_and_residue_from_atomic_equal_for_mod_or_builtin(first_atomic)
    else {
        return false;
    };
    let Some(modulus_value) = positive_integer_number_to_usize_for_mod_or_builtin(first_modulus)
    else {
        return false;
    };
    if modulus_value <= 1 || modulus_value != or_fact.facts.len() {
        return false;
    }

    let mut seen_residues = vec![false; modulus_value];
    let Some(first_residue_value) =
        nonnegative_integer_number_to_usize_for_mod_or_builtin(first_residue)
    else {
        return false;
    };
    if first_residue_value >= modulus_value {
        return false;
    }
    seen_residues[first_residue_value] = true;

    for fact in or_fact.facts.iter().skip(1) {
        let AndChainAtomicFact::AtomicFact(atomic) = fact else {
            return false;
        };
        let Some((obj, modulus, residue)) =
            mod_obj_and_residue_from_atomic_equal_for_mod_or_builtin(atomic)
        else {
            return false;
        };
        if !objs_equal_by_display_string(obj, first_obj)
            || !objs_equal_by_display_string(
                &Obj::Number(modulus.clone()),
                &Obj::Number(first_modulus.clone()),
            )
        {
            return false;
        }
        let Some(residue_value) = nonnegative_integer_number_to_usize_for_mod_or_builtin(residue)
        else {
            return false;
        };
        if residue_value >= modulus_value || seen_residues[residue_value] {
            return false;
        }
        seen_residues[residue_value] = true;
    }

    seen_residues.iter().all(|seen| *seen)
}

fn integer_literal_i128_for_or_builtin(obj: &Obj) -> Option<i128> {
    let Obj::Number(n) = obj else {
        return None;
    };
    n.normalized_value.parse::<i128>().ok()
}

fn integer_successor_value_for_or_builtin(base: &Obj, offset: usize) -> Obj {
    if offset == 0 {
        return base.clone();
    }
    if let Some(base_value) = integer_literal_i128_for_or_builtin(base) {
        return Number::new((base_value + offset as i128).to_string()).into();
    }
    Add::new(base.clone(), Number::new(offset.to_string()).into()).into()
}

fn equality_branch_matches_subject_and_value(
    atomic: &AtomicFact,
    subject: &Obj,
    value: &Obj,
) -> bool {
    let AtomicFact::EqualFact(eq) = atomic else {
        return false;
    };
    (objs_equal_by_display_string(&eq.left, subject)
        && objs_equal_by_display_string(&eq.right, value))
        || (objs_equal_by_display_string(&eq.right, subject)
            && objs_equal_by_display_string(&eq.left, value))
}

fn strict_tail_branch_matches_subject_and_value(
    atomic: &AtomicFact,
    subject: &Obj,
    tail_value: &Obj,
) -> bool {
    match atomic {
        AtomicFact::GreaterFact(g) => {
            objs_equal_by_display_string(&g.left, subject)
                && objs_equal_by_display_string(&g.right, tail_value)
        }
        AtomicFact::LessFact(l) => {
            objs_equal_by_display_string(&l.right, subject)
                && objs_equal_by_display_string(&l.left, tail_value)
        }
        _ => false,
    }
}

fn integer_successor_tail_or_pattern(or_fact: &OrFact) -> Option<(Obj, Obj)> {
    if or_fact.facts.len() < 2 {
        return None;
    }
    let AndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(first_eq)) = &or_fact.facts[0] else {
        return None;
    };
    let subject_base_candidates = [
        (first_eq.left.clone(), first_eq.right.clone()),
        (first_eq.right.clone(), first_eq.left.clone()),
    ];
    for (subject, base) in subject_base_candidates {
        if integer_successor_tail_or_pattern_with_subject_base(or_fact, &subject, &base) {
            return Some((subject, base));
        }
    }
    None
}

fn integer_successor_tail_or_pattern_with_subject_base(
    or_fact: &OrFact,
    subject: &Obj,
    base: &Obj,
) -> bool {
    let equality_count = or_fact.facts.len() - 1;
    for (offset, fact) in or_fact.facts.iter().take(equality_count).enumerate() {
        let AndChainAtomicFact::AtomicFact(atomic) = fact else {
            return false;
        };
        let value = integer_successor_value_for_or_builtin(base, offset);
        if !equality_branch_matches_subject_and_value(atomic, subject, &value) {
            return false;
        }
    }
    let tail_value = integer_successor_value_for_or_builtin(base, equality_count - 1);
    let AndChainAtomicFact::AtomicFact(last_atomic) = &or_fact.facts[equality_count] else {
        return false;
    };
    strict_tail_branch_matches_subject_and_value(last_atomic, subject, &tail_value)
}

fn obj_is_literal_zero_for_or_builtin(obj: &Obj) -> bool {
    match obj {
        Obj::Number(n) => n.normalized_value == "0",
        _ => false,
    }
}

fn nonzero_operand_from_atomic_fact_for_square_sum_or_builtin(atomic: &AtomicFact) -> Option<Obj> {
    let AtomicFact::NotEqualFact(not_equal) = atomic else {
        return None;
    };
    if obj_is_literal_zero_for_or_builtin(&not_equal.right) {
        return Some(not_equal.left.clone());
    }
    if obj_is_literal_zero_for_or_builtin(&not_equal.left) {
        return Some(not_equal.right.clone());
    }
    None
}

fn square_pow_sum_not_equal_zero_fact_for_or_builtin(
    left_base: Obj,
    right_base: Obj,
    line_file: LineFile,
) -> AtomicFact {
    let two_obj: Obj = Number::new("2".to_string()).into();
    let zero_obj: Obj = Number::new("0".to_string()).into();
    let left_square: Obj = Pow::new(left_base, two_obj.clone()).into();
    let right_square: Obj = Pow::new(right_base, two_obj).into();
    let square_sum: Obj = Add::new(left_square, right_square).into();
    NotEqualFact::new(square_sum, zero_obj, line_file).into()
}

fn square_mul_sum_not_equal_zero_fact_for_or_builtin(
    left_base: Obj,
    right_base: Obj,
    line_file: LineFile,
) -> AtomicFact {
    let zero_obj: Obj = Number::new("0".to_string()).into();
    let left_square: Obj = Mul::new(left_base.clone(), left_base).into();
    let right_square: Obj = Mul::new(right_base.clone(), right_base).into();
    let square_sum: Obj = Add::new(left_square, right_square).into();
    NotEqualFact::new(square_sum, zero_obj, line_file).into()
}

impl Runtime {
    pub fn verify_or_fact(
        &mut self,
        or_fact: &OrFact,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        if let Some(cached_result) =
            self.verify_fact_from_cache_using_display_string(&or_fact.clone().into())
        {
            return Ok(cached_result);
        }

        if !verify_state.well_defined_already_verified {
            if let Err(e) = self.verify_or_fact_well_defined(or_fact, verify_state) {
                return Err({
                    VerifyRuntimeError(RuntimeErrorStruct::new(
                        Some(Fact::from(or_fact.clone()).into_stmt()),
                        String::new(),
                        or_fact.line_file.clone(),
                        Some(e),
                        vec![],
                    ))
                    .into()
                });
            }
        }

        let verify_state_for_children = verify_state.make_state_with_req_ok_set_to_true();

        if or_fact.facts.len() == 2 {
            if let (
                AndChainAtomicFact::AtomicFact(first_atomic),
                AndChainAtomicFact::AtomicFact(second_atomic),
            ) = (&or_fact.facts[0], &or_fact.facts[1])
            {
                if first_atomic.make_reversed().to_string() == second_atomic.to_string() {
                    return Ok(
                        (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                            or_fact.clone().into(),
                            "or: complementary atomic facts (make_reversed first equals second)"
                                .to_string(),
                            Vec::new(),
                        ))
                        .into(),
                    );
                }
                if order_split_or_is_exhaustive_pair(first_atomic, second_atomic)
                    || order_split_or_is_exhaustive_pair(second_atomic, first_atomic)
                {
                    return Ok(
                        (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                            or_fact.clone().into(),
                            "or: complementary order relations (strict vs non-strict) on the same terms"
                                .to_string(),
                            Vec::new(),
                        ))
                        .into(),
                    );
                }
                if let Some(weak_bound) =
                    equality_and_strict_order_need_weak_bound(first_atomic, second_atomic).or_else(
                        || equality_and_strict_order_need_weak_bound(second_atomic, first_atomic),
                    )
                {
                    let weak_result = self.verify_non_equational_known_then_builtin_rules_only(
                        &weak_bound,
                        verify_state,
                    )?;
                    if weak_result.is_true() {
                        return Ok(
                            (FactualStmtSuccess::new_with_verified_by_builtin_rules_label_and_steps(
                                or_fact.clone().into(),
                                InferResult::new(),
                                "or: equality plus strict order covers a known weak order".to_string(),
                                vec![weak_result],
                            ))
                            .into(),
                        );
                    }
                }
                if abs_sign_split_or_is_exhaustive_pair(first_atomic, second_atomic)
                    || abs_sign_split_or_is_exhaustive_pair(second_atomic, first_atomic)
                {
                    return Ok(
                        (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                            or_fact.clone().into(),
                            "or: abs(x) is x or -x".to_string(),
                            Vec::new(),
                        ))
                        .into(),
                    );
                }
            }
        }

        if mod_positive_integer_residue_or_is_exhaustive(or_fact) {
            return Ok(
                (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    or_fact.clone().into(),
                    "or: complete residue classes modulo a positive integer".to_string(),
                    Vec::new(),
                ))
                .into(),
            );
        }

        if let Some(result) =
            self.try_verify_integer_successor_tail_or_from_lower_bound(or_fact, verify_state)?
        {
            return Ok(result);
        }

        if let Some(result) =
            self.try_verify_component_nonzero_or_from_known_square_sum_not_equal_zero(or_fact)?
        {
            return Ok(result);
        }

        for fact in or_fact.facts.iter() {
            let result = self.verify_and_chain_atomic_fact(fact, &verify_state_for_children)?;
            if result.is_true() {
                return Ok((FactualStmtSuccess::new_with_verified_by_known_fact(
                    or_fact.clone().into(),
                    VerifiedByResult::wrap_bys(vec![VerifiedBysEnum::cited_fact(
                        or_fact.clone().into(),
                        fact.clone().into(),
                        None,
                    )]),
                    Vec::new(),
                ))
                .into());
            }
        }

        let result = self.verify_or_fact_with_known_or_facts(or_fact)?;
        if result.is_true() {
            return Ok(result);
        }

        let result = self.verify_or_fact_with_known_forall(or_fact, verify_state)?;
        if result.is_true() {
            return Ok(result);
        }

        Ok(StmtUnknown::new().into())
    }

    /// Integer lower-bound split into finitely many successor equalities plus a strict tail.
    /// Applies when `x $in Z`, `a $in Z`, and `x >= a` are known or builtin-provable.
    /// Example: from `x $in Z` and `x >= 1`, infer `x = 1 or x = 2 or x = 3 or x > 3`.
    fn try_verify_integer_successor_tail_or_from_lower_bound(
        &mut self,
        or_fact: &OrFact,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let Some((subject, base)) = integer_successor_tail_or_pattern(or_fact) else {
            return Ok(None);
        };

        let line_file = or_fact.line_file.clone();
        let z_set: Obj = StandardSet::Z.into();
        let prerequisites: Vec<AtomicFact> = vec![
            InFact::new(subject.clone(), z_set.clone(), line_file.clone()).into(),
            InFact::new(base.clone(), z_set, line_file.clone()).into(),
            GreaterEqualFact::new(subject, base, line_file).into(),
        ];
        let mut steps = Vec::with_capacity(prerequisites.len());
        for prerequisite in prerequisites {
            let result = self
                .verify_non_equational_known_then_builtin_rules_only(&prerequisite, verify_state)?;
            if result.is_unknown() {
                return Ok(None);
            }
            steps.push(result);
        }

        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_label_and_steps(
                or_fact.clone().into(),
                InferResult::new(),
                "or: integer lower bound split into finite successors and strict tail".to_string(),
                steps,
            )
            .into(),
        ))
    }

    fn try_verify_component_nonzero_or_from_known_square_sum_not_equal_zero(
        &mut self,
        or_fact: &OrFact,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if or_fact.facts.len() != 2 {
            return Ok(None);
        }
        let (
            AndChainAtomicFact::AtomicFact(first_atomic),
            AndChainAtomicFact::AtomicFact(second_atomic),
        ) = (&or_fact.facts[0], &or_fact.facts[1])
        else {
            return Ok(None);
        };
        let Some(first_base) =
            nonzero_operand_from_atomic_fact_for_square_sum_or_builtin(first_atomic)
        else {
            return Ok(None);
        };
        let Some(second_base) =
            nonzero_operand_from_atomic_fact_for_square_sum_or_builtin(second_atomic)
        else {
            return Ok(None);
        };

        let line_file = or_fact.line_file.clone();
        let candidates = vec![
            square_pow_sum_not_equal_zero_fact_for_or_builtin(
                first_base.clone(),
                second_base.clone(),
                line_file.clone(),
            ),
            square_pow_sum_not_equal_zero_fact_for_or_builtin(
                second_base.clone(),
                first_base.clone(),
                line_file.clone(),
            ),
            square_mul_sum_not_equal_zero_fact_for_or_builtin(
                first_base.clone(),
                second_base.clone(),
                line_file.clone(),
            ),
            square_mul_sum_not_equal_zero_fact_for_or_builtin(second_base, first_base, line_file),
        ];

        for candidate in candidates {
            let result =
                self.verify_non_equational_atomic_fact_with_known_atomic_facts(&candidate)?;
            if result.is_true() {
                return Ok(Some(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_label_and_steps(
                        or_fact.clone().into(),
                        InferResult::new(),
                        "or: square sum nonzero implies one component nonzero".to_string(),
                        vec![result],
                    )
                    .into(),
                ));
            }
        }
        Ok(None)
    }

    pub fn verify_or_fact_with_known_or_facts(
        &mut self,
        or_fact: &OrFact,
    ) -> Result<StmtResult, RuntimeError> {
        let args_in_or_fact = or_fact.get_args_from_fact_ref();
        let mut all_objs_equal_to_each_arg: Vec<Vec<String>> = Vec::new();
        for arg in args_in_or_fact.iter() {
            let mut all_objs_equal_to_current_arg =
                self.get_all_objs_equal_to_given(&arg.to_string());
            if all_objs_equal_to_current_arg.is_empty() {
                all_objs_equal_to_current_arg.push(arg.to_string());
            }
            all_objs_equal_to_each_arg.push(all_objs_equal_to_current_arg);
        }

        for environment in self.iter_environments_from_top() {
            let result = Self::verify_or_fact_with_known_or_facts_with_facts_in_environment(
                environment,
                or_fact,
                &all_objs_equal_to_each_arg,
            )?;
            if result.is_true() {
                return Ok(result);
            }
        }

        Ok((StmtUnknown::new()).into())
    }

    pub fn verify_or_fact_with_known_or_facts_with_facts_in_environment(
        environment: &Environment,
        or_fact: &OrFact,
        all_objs_equal_to_each_arg: &Vec<Vec<String>>,
    ) -> Result<StmtResult, RuntimeError> {
        if let Some(known_or_facts) = environment.known_or_facts.get(&or_fact.key()) {
            for known_or_fact in known_or_facts.iter() {
                if !Self::_verify_or_fact_the_same_type_ref(known_or_fact, or_fact)? {
                    continue;
                }
                let mut all_args_match = true;
                let known_args = known_or_fact.get_args_from_fact_ref();
                let given_args = or_fact.get_args_from_fact_ref();
                for (index, known_arg) in known_args.iter().enumerate() {
                    let given_arg = given_args[index];
                    let known_arg_string = known_arg.to_string();

                    if known_arg_string != given_arg.to_string()
                        && !all_objs_equal_to_each_arg[index].contains(&known_arg_string)
                    {
                        all_args_match = false;
                        break;
                    }
                }

                if all_args_match {
                    return Ok((FactualStmtSuccess::new_with_verified_by_known_fact(
                        or_fact.clone().into(),
                        VerifiedByResult::wrap_bys(vec![VerifiedBysEnum::cited_fact(
                            or_fact.clone().into(),
                            known_or_fact.clone().into(),
                            None,
                        )]),
                        Vec::new(),
                    ))
                    .into());
                }
            }
        }

        return Ok((StmtUnknown::new()).into());
    }
}
