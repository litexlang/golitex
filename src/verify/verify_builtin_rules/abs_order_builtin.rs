use super::order_normalize::normalize_positive_order_atomic_fact;
use crate::prelude::*;

impl Runtime {
    pub(crate) fn verify_abs_order_builtin_rule(
        &mut self,
        atomic_fact: &AtomicFact,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let Some(norm) = normalize_positive_order_atomic_fact(atomic_fact) else {
            return Ok(None);
        };
        let AtomicFact::LessEqualFact(f) = &norm else {
            return Ok(None);
        };
        if let Some(result) = self.try_verify_abs_basic_lower_bound(f, atomic_fact)? {
            return Ok(Some(result));
        }
        if let Some(result) = self.try_verify_abs_triangle(f, atomic_fact)? {
            return Ok(Some(result));
        }
        if let Some(result) = self.try_verify_abs_reverse_triangle(f, atomic_fact)? {
            return Ok(Some(result));
        }
        if let Some(result) =
            self.try_verify_abs_upper_bound(&f.left, &f.right, &f.line_file, atomic_fact, false)?
        {
            return Ok(Some(result));
        }
        if let Some(result) = self.try_verify_abs_lower_bound_from_abs_compare(
            &f.left,
            &f.right,
            &f.line_file,
            atomic_fact,
            false,
        )? {
            return Ok(Some(result));
        }
        Ok(None)
    }

    pub(crate) fn verify_abs_order_strict_builtin_rule(
        &mut self,
        atomic_fact: &AtomicFact,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let Some(norm) = normalize_positive_order_atomic_fact(atomic_fact) else {
            return Ok(None);
        };
        let AtomicFact::LessFact(f) = &norm else {
            return Ok(None);
        };
        if let Some(result) =
            self.try_verify_abs_upper_bound(&f.left, &f.right, &f.line_file, atomic_fact, true)?
        {
            return Ok(Some(result));
        }
        if let Some(result) = self.try_verify_abs_lower_bound_from_abs_compare(
            &f.left,
            &f.right,
            &f.line_file,
            atomic_fact,
            true,
        )? {
            return Ok(Some(result));
        }
        Ok(None)
    }
}

fn literal_neg_one_obj() -> Obj {
    Obj::Number(Number::new("-1".to_string()))
}

fn obj_is_literal_neg_one(obj: &Obj) -> bool {
    match obj {
        Obj::Number(n) => n.normalized_value == "-1",
        _ => false,
    }
}

fn neg_obj(obj: &Obj) -> Obj {
    Mul::new(literal_neg_one_obj(), obj.clone()).into()
}

fn objs_equal(a: &Obj, b: &Obj) -> bool {
    a.to_string() == b.to_string()
}

fn obj_is_negation_of(obj: &Obj, expected_arg: &Obj) -> bool {
    match obj {
        Obj::Mul(m) => {
            (obj_is_literal_neg_one(m.left.as_ref()) && objs_equal(m.right.as_ref(), expected_arg))
                || (obj_is_literal_neg_one(m.right.as_ref())
                    && objs_equal(m.left.as_ref(), expected_arg))
        }
        _ => false,
    }
}

fn obj_is_abs_of(obj: &Obj, arg: &Obj) -> bool {
    match obj {
        Obj::Abs(abs) => objs_equal(abs.arg.as_ref(), arg),
        _ => false,
    }
}

fn obj_is_add_of_abs_pair(obj: &Obj, x: &Obj, y: &Obj) -> bool {
    let Obj::Add(add) = obj else {
        return false;
    };
    (obj_is_abs_of(add.left.as_ref(), x) && obj_is_abs_of(add.right.as_ref(), y))
        || (obj_is_abs_of(add.left.as_ref(), y) && obj_is_abs_of(add.right.as_ref(), x))
}

fn obj_is_abs_of_add_pair(obj: &Obj, x: &Obj, y: &Obj) -> bool {
    let Obj::Abs(abs) = obj else {
        return false;
    };
    let Obj::Add(add) = abs.arg.as_ref() else {
        return false;
    };
    (objs_equal(add.left.as_ref(), x) && objs_equal(add.right.as_ref(), y))
        || (objs_equal(add.left.as_ref(), y) && objs_equal(add.right.as_ref(), x))
}

fn obj_is_abs_of_sub_pair(obj: &Obj, x: &Obj, y: &Obj) -> bool {
    let Obj::Abs(abs) = obj else {
        return false;
    };
    let Obj::Sub(sub) = abs.arg.as_ref() else {
        return false;
    };
    objs_equal(sub.left.as_ref(), x) && objs_equal(sub.right.as_ref(), y)
}

fn abs_obj(arg: Obj) -> Obj {
    Abs::new(arg).into()
}

fn abs_order_subgoal(left: Obj, right: Obj, line_file: LineFile, strict: bool) -> AtomicFact {
    if strict {
        LessFact::new(left, right, line_file).into()
    } else {
        LessEqualFact::new(left, right, line_file).into()
    }
}

fn peel_negation(obj: &Obj) -> Option<&Obj> {
    match obj {
        Obj::Mul(m) => {
            if obj_is_literal_neg_one(m.left.as_ref()) {
                Some(m.right.as_ref())
            } else if obj_is_literal_neg_one(m.right.as_ref()) {
                Some(m.left.as_ref())
            } else {
                None
            }
        }
        _ => None,
    }
}

fn peel_abs(obj: &Obj) -> Option<&Obj> {
    match obj {
        Obj::Abs(abs) => Some(abs.arg.as_ref()),
        _ => None,
    }
}

impl Runtime {
    fn verify_abs_order_subgoal(&mut self, fact: AtomicFact) -> Result<StmtResult, RuntimeError> {
        self.verify_non_equational_known_then_builtin_rules_only(&fact, &VerifyState::new(0, true))
    }

    // Absolute value bounds: x <= abs(x) and -x <= abs(x).
    // Example: `forall x R: x <= abs(x)`.
    fn try_verify_abs_basic_lower_bound(
        &mut self,
        f: &LessEqualFact,
        atomic_fact: &AtomicFact,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let Obj::Abs(abs) = &f.right else {
            return Ok(None);
        };
        if !objs_equal(&f.left, abs.arg.as_ref()) && !obj_is_negation_of(&f.left, abs.arg.as_ref())
        {
            return Ok(None);
        }
        Ok(Some(StmtResult::FactualStmtSuccess(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                atomic_fact.clone().into(),
                "abs: x <= abs(x) and -x <= abs(x)".to_string(),
                Vec::new(),
            ),
        )))
    }

    // Absolute value upper bound: abs(x) <= b from x <= b and -x <= b.
    // Strict form: abs(x) < b from x < b and -x < b.
    // Example: `forall x, b R: x <= b, -x <= b => abs(x) <= b`.
    fn try_verify_abs_upper_bound(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: &LineFile,
        atomic_fact: &AtomicFact,
        strict: bool,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let Obj::Abs(abs) = left else {
            return Ok(None);
        };
        let arg = abs.arg.as_ref();
        let arg_le_bound = abs_order_subgoal(arg.clone(), right.clone(), line_file.clone(), strict);
        let neg_arg_le_bound =
            abs_order_subgoal(neg_obj(arg), right.clone(), line_file.clone(), strict);
        let r1 = self.verify_abs_order_subgoal(arg_le_bound)?;
        if !r1.is_true() {
            return Ok(None);
        }
        let r2 = self.verify_abs_order_subgoal(neg_arg_le_bound)?;
        if !r2.is_true() {
            return Ok(None);
        }
        let rule = if strict {
            "abs: abs(x) < b from x < b and -x < b"
        } else {
            "abs: abs(x) <= b from x <= b and -x <= b"
        };
        Ok(Some(StmtResult::FactualStmtSuccess(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                atomic_fact.clone().into(),
                rule.to_string(),
                vec![r1, r2],
            ),
        )))
    }

    // Converse of abs upper bound: sandwich bounds from abs(x) <= abs(y) (or strict <).
    // Examples:
    // `forall x, y R: abs(x) <= abs(y) => -abs(y) <= x <= abs(y)`
    // `forall x, y R: abs(x) <= abs(y), 0 <= y => -y <= x <= y`
    // `forall x, y R: abs(x) <= abs(y), y <= 0 => y <= x <= -y`
    fn try_verify_abs_lower_bound_from_abs_compare(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: &LineFile,
        atomic_fact: &AtomicFact,
        strict: bool,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let rule_suffix = if strict { " (strict)" } else { "" };
        let zero: Obj = Number::new("0".to_string()).into();

        // -abs(y) <= x from abs(x) <= abs(y); or -y <= x when 0 <= y.
        if let Some(inner) = peel_negation(left) {
            if let Some(y) = peel_abs(inner) {
                if let Some(r) =
                    self.verify_known_abs_compare(right, &abs_obj(y.clone()), line_file, strict)?
                {
                    let rule = format!(
                        "abs: -abs(y) {} x from abs(x) {} abs(y){}",
                        if strict { "<" } else { "<=" },
                        if strict { "<" } else { "<=" },
                        rule_suffix
                    );
                    return Ok(Some(StmtResult::FactualStmtSuccess(
                        FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                            atomic_fact.clone().into(),
                            rule,
                            vec![r],
                        ),
                    )));
                }
            } else {
                let y = inner;
                if let Some(r) =
                    self.verify_known_abs_compare(right, &abs_obj(y.clone()), line_file, strict)?
                {
                    let ge_y: AtomicFact =
                        GreaterEqualFact::new(y.clone(), zero.clone(), line_file.clone()).into();
                    let r_sign = self.verify_abs_order_subgoal(ge_y)?;
                    if r_sign.is_true() {
                        let rule = format!(
                            "abs: -y {} x from abs(x) {} abs(y) and 0 <= y{}",
                            if strict { "<" } else { "<=" },
                            if strict { "<" } else { "<=" },
                            rule_suffix
                        );
                        return Ok(Some(StmtResult::FactualStmtSuccess(
                            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                                atomic_fact.clone().into(),
                                rule,
                                vec![r, r_sign],
                            ),
                        )));
                    }
                }
            }
        }

        // x <= bound or x < bound from abs(x) <= bound (or strict).
        if let Some(r) = self.verify_known_abs_compare(left, right, line_file, strict)? {
            let rule = format!(
                "abs: x {} b from abs(x) {} b{}",
                if strict { "<" } else { "<=" },
                if strict { "<" } else { "<=" },
                rule_suffix
            );
            return Ok(Some(StmtResult::FactualStmtSuccess(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    atomic_fact.clone().into(),
                    rule,
                    vec![r],
                ),
            )));
        }

        // -x <= bound or -x < bound from abs(x) <= bound (or strict).
        if let Some(arg) = peel_negation(left) {
            if let Some(r) = self.verify_known_abs_compare(arg, right, line_file, strict)? {
                let rule = format!(
                    "abs: -x {} b from abs(x) {} b{}",
                    if strict { "<" } else { "<=" },
                    if strict { "<" } else { "<=" },
                    rule_suffix
                );
                return Ok(Some(StmtResult::FactualStmtSuccess(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        atomic_fact.clone().into(),
                        rule,
                        vec![r],
                    ),
                )));
            }
        }

        // y <= x from abs(x) <= abs(y) and y <= 0.
        if let Some(r) =
            self.verify_known_abs_compare(right, &abs_obj(left.clone()), line_file, strict)?
        {
            let le_y: AtomicFact =
                LessEqualFact::new(left.clone(), zero.clone(), line_file.clone()).into();
            let r_sign = self.verify_abs_order_subgoal(le_y)?;
            if r_sign.is_true() {
                let rule = format!(
                    "abs: y {} x from abs(x) {} abs(y) and y <= 0{}",
                    if strict { "<" } else { "<=" },
                    if strict { "<" } else { "<=" },
                    rule_suffix
                );
                return Ok(Some(StmtResult::FactualStmtSuccess(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        atomic_fact.clone().into(),
                        rule,
                        vec![r, r_sign],
                    ),
                )));
            }
        }

        // x <= -y from abs(x) <= abs(y) and y <= 0.
        if let Some(y) = peel_negation(right) {
            if let Some(r) =
                self.verify_known_abs_compare(left, &abs_obj(y.clone()), line_file, strict)?
            {
                let le_y: AtomicFact =
                    LessEqualFact::new(y.clone(), zero.clone(), line_file.clone()).into();
                let r_sign = self.verify_abs_order_subgoal(le_y)?;
                if r_sign.is_true() {
                    let rule = format!(
                        "abs: x {} -y from abs(x) {} abs(y) and y <= 0{}",
                        if strict { "<" } else { "<=" },
                        if strict { "<" } else { "<=" },
                        rule_suffix
                    );
                    return Ok(Some(StmtResult::FactualStmtSuccess(
                        FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                            atomic_fact.clone().into(),
                            rule,
                            vec![r, r_sign],
                        ),
                    )));
                }
            }
        }

        // x <= y from abs(x) <= abs(y) and 0 <= y.
        if let Some(r) =
            self.verify_known_abs_compare(left, &abs_obj(right.clone()), line_file, strict)?
        {
            let ge_y: AtomicFact =
                GreaterEqualFact::new(right.clone(), zero.clone(), line_file.clone()).into();
            let r_sign = self.verify_abs_order_subgoal(ge_y)?;
            if r_sign.is_true() {
                let rule = format!(
                    "abs: x {} y from abs(x) {} abs(y) and 0 <= y{}",
                    if strict { "<" } else { "<=" },
                    if strict { "<" } else { "<=" },
                    rule_suffix
                );
                return Ok(Some(StmtResult::FactualStmtSuccess(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        atomic_fact.clone().into(),
                        rule,
                        vec![r, r_sign],
                    ),
                )));
            }
        }

        Ok(None)
    }

    fn verify_known_abs_compare(
        &mut self,
        arg: &Obj,
        bound: &Obj,
        line_file: &LineFile,
        strict: bool,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let fact = abs_order_subgoal(
            abs_obj(arg.clone()),
            bound.clone(),
            line_file.clone(),
            strict,
        );
        for environment in self.iter_environments_from_top() {
            if let Some(known_facts_map) = environment
                .known_atomic_facts_with_2_args
                .get(&(fact.key(), fact.is_true()))
            {
                let args = fact.args();
                let key = (args[0].to_string(), args[1].to_string());
                if let Some(known_fact) = known_facts_map.get(&key) {
                    return Ok(Some(StmtResult::FactualStmtSuccess(
                        FactualStmtSuccess::new_with_verified_by_known_fact(
                            fact.clone().into(),
                            VerifiedByResult::cited_fact(
                                fact.clone().into(),
                                known_fact.clone().into(),
                                None,
                            ),
                            Vec::new(),
                        ),
                    )));
                }
            }
        }
        Ok(None)
    }

    // Triangle inequality for addition and subtraction.
    // Examples: `abs(x + y) <= abs(x) + abs(y)`, `abs(x - y) <= abs(x) + abs(y)`.
    fn try_verify_abs_triangle(
        &mut self,
        f: &LessEqualFact,
        atomic_fact: &AtomicFact,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let Obj::Abs(abs) = &f.left else {
            return Ok(None);
        };
        let ok = match abs.arg.as_ref() {
            Obj::Add(add) => {
                obj_is_add_of_abs_pair(&f.right, add.left.as_ref(), add.right.as_ref())
            }
            Obj::Sub(sub) => {
                obj_is_add_of_abs_pair(&f.right, sub.left.as_ref(), sub.right.as_ref())
            }
            _ => false,
        };
        if !ok {
            return Ok(None);
        }
        Ok(Some(StmtResult::FactualStmtSuccess(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                atomic_fact.clone().into(),
                "abs: triangle inequality".to_string(),
                Vec::new(),
            ),
        )))
    }

    // Weak reverse triangle inequality.
    // Examples: `abs(x) - abs(y) <= abs(x + y)`, `abs(x) - abs(y) <= abs(x - y)`.
    fn try_verify_abs_reverse_triangle(
        &mut self,
        f: &LessEqualFact,
        atomic_fact: &AtomicFact,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let Obj::Sub(sub) = &f.left else {
            return Ok(None);
        };
        let (Obj::Abs(left_abs), Obj::Abs(right_abs)) = (sub.left.as_ref(), sub.right.as_ref())
        else {
            return Ok(None);
        };
        let x = left_abs.arg.as_ref();
        let y = right_abs.arg.as_ref();
        if !obj_is_abs_of_add_pair(&f.right, x, y) && !obj_is_abs_of_sub_pair(&f.right, x, y) {
            return Ok(None);
        }
        Ok(Some(StmtResult::FactualStmtSuccess(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                atomic_fact.clone().into(),
                "abs: weak reverse triangle inequality".to_string(),
                Vec::new(),
            ),
        )))
    }
}
