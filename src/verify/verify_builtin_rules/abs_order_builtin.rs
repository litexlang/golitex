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
        if let Some(result) = self.try_verify_abs_upper_bound(f, atomic_fact)? {
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
    // Example: `forall x, b R: x <= b, -x <= b => abs(x) <= b`.
    fn try_verify_abs_upper_bound(
        &mut self,
        f: &LessEqualFact,
        atomic_fact: &AtomicFact,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let Obj::Abs(abs) = &f.left else {
            return Ok(None);
        };
        let arg = abs.arg.as_ref();
        let arg_le_bound: AtomicFact =
            LessEqualFact::new(arg.clone(), f.right.clone(), f.line_file.clone()).into();
        let neg_arg_le_bound: AtomicFact =
            LessEqualFact::new(neg_obj(arg), f.right.clone(), f.line_file.clone()).into();
        let r1 = self.verify_abs_order_subgoal(arg_le_bound)?;
        if !r1.is_true() {
            return Ok(None);
        }
        let r2 = self.verify_abs_order_subgoal(neg_arg_le_bound)?;
        if !r2.is_true() {
            return Ok(None);
        }
        Ok(Some(StmtResult::FactualStmtSuccess(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                atomic_fact.clone().into(),
                "abs: abs(x) <= b from x <= b and -x <= b".to_string(),
                vec![r1, r2],
            ),
        )))
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
