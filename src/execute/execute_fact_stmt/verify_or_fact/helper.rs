use crate::ast::fact::negate_atomic_fact;
use crate::ast::fact::{
    AtomicFact, EqualFact, Fact, GreaterEqualFact, InFact, LessEqualFact, NotEqualFact,
};
use crate::ast::obj::{
    Abs, Add, ArithmeticOperator, IntegerOperator, Literal, Mod, Mul, Neg, Number, Obj, Pow,
    StandardSet, Sub,
};
use crate::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::runtime_ids::FactId;
use crate::runtime::{Runtime, RuntimeResult};

pub(super) fn objs_same(left: &Obj, right: &Obj) -> bool {
    left.ir() == right.ir()
}

// Equality may flip operands relative to the order pair.
pub(super) fn equal_matches_pair(eq: &EqualFact, left: &Obj, right: &Obj) -> bool {
    (objs_same(&eq.left, left) && objs_same(&eq.right, right))
        || (objs_same(&eq.left, right) && objs_same(&eq.right, left))
}

pub(super) fn is_number_obj(obj: &Obj, value: &str) -> bool {
    matches!(
        obj,
        Obj::Literal(Literal::Number(Number {
            normalized_value,
        })) if normalized_value == value
    )
}

// Classical excluded middle: each atomic is the negation of the other (IR).
// Example: `1 = 1` and `1 != 1`.
pub(super) fn complementary_atomic_pair(left: &AtomicFact, right: &AtomicFact) -> bool {
    let Some(negated_left) = negate_atomic_fact(left, FactId::new(0)) else {
        return false;
    };
    if negated_left.ir() == right.ir() {
        return true;
    }
    let Some(negated_right) = negate_atomic_fact(right, FactId::new(0)) else {
        return false;
    };
    negated_right.ir() == left.ir()
}

// Match `abs(x) = x` (either equality order). Returns `x`.
pub(super) fn equal_abs_equals_arg(eq: &EqualFact) -> Option<Obj> {
    match (&eq.left, &eq.right) {
        (Obj::ArithmeticOperator(ArithmeticOperator::Abs(Abs { arg })), other)
            if objs_same(arg.as_ref(), other) =>
        {
            Some(arg.as_ref().clone())
        }
        (other, Obj::ArithmeticOperator(ArithmeticOperator::Abs(Abs { arg })))
            if objs_same(arg.as_ref(), other) =>
        {
            Some(arg.as_ref().clone())
        }
        _ => None,
    }
}

fn is_neg_of(obj: &Obj, expected: &Obj) -> bool {
    matches!(
        obj,
        Obj::ArithmeticOperator(ArithmeticOperator::Neg(Neg { arg }))
            if objs_same(arg.as_ref(), expected)
    )
}

// Match `abs(x) = (-x)` (either equality order). Returns `x`.
pub(super) fn equal_abs_equals_neg_arg(eq: &EqualFact) -> Option<Obj> {
    match (&eq.left, &eq.right) {
        (Obj::ArithmeticOperator(ArithmeticOperator::Abs(Abs { arg })), other)
            if is_neg_of(other, arg.as_ref()) =>
        {
            Some(arg.as_ref().clone())
        }
        (other, Obj::ArithmeticOperator(ArithmeticOperator::Abs(Abs { arg })))
            if is_neg_of(other, arg.as_ref()) =>
        {
            Some(arg.as_ref().clone())
        }
        _ => None,
    }
}

// Pure shape: `abs(x) = x or abs(x) = (-x)` in either branch order.
pub(super) fn match_abs_sign_split_arg(first: &EqualFact, second: &EqualFact) -> Option<Obj> {
    if let (Some(arg_self), Some(arg_neg)) =
        (equal_abs_equals_arg(first), equal_abs_equals_neg_arg(second))
    {
        if objs_same(&arg_self, &arg_neg) {
            return Some(arg_self);
        }
    }
    if let (Some(arg_neg), Some(arg_self)) =
        (equal_abs_equals_neg_arg(first), equal_abs_equals_arg(second))
    {
        if objs_same(&arg_self, &arg_neg) {
            return Some(arg_self);
        }
    }
    None
}

// Match `a < b` with `a >= b` (same endpoints). Returns `(a, b)`.
// Covers either atomic order; callers prove both `$in R`.
pub(super) fn match_less_or_greater_equal_operands(
    first: &AtomicFact,
    second: &AtomicFact,
) -> Option<(Obj, Obj)> {
    match (first, second) {
        (AtomicFact::LessFact(l), AtomicFact::GreaterEqualFact(ge))
            if objs_same(&l.left, &ge.left) && objs_same(&l.right, &ge.right) =>
        {
            Some((l.left.clone(), l.right.clone()))
        }
        (AtomicFact::GreaterEqualFact(ge), AtomicFact::LessFact(l))
            if objs_same(&l.left, &ge.left) && objs_same(&l.right, &ge.right) =>
        {
            Some((l.left.clone(), l.right.clone()))
        }
        _ => None,
    }
}

// Match `a > b` with `a <= b` (same endpoints). Returns `(a, b)`.
pub(super) fn match_greater_or_less_equal_operands(
    first: &AtomicFact,
    second: &AtomicFact,
) -> Option<(Obj, Obj)> {
    match (first, second) {
        (AtomicFact::GreaterFact(g), AtomicFact::LessEqualFact(le))
            if objs_same(&g.left, &le.left) && objs_same(&g.right, &le.right) =>
        {
            Some((g.left.clone(), g.right.clone()))
        }
        (AtomicFact::LessEqualFact(le), AtomicFact::GreaterFact(g))
            if objs_same(&g.left, &le.left) && objs_same(&g.right, &le.right) =>
        {
            Some((g.left.clone(), g.right.clone()))
        }
        _ => None,
    }
}

// Match `a <= b` with `a >= b` (same endpoints). Returns `(a, b)`.
pub(super) fn match_weak_order_le_or_ge_operands(
    first: &AtomicFact,
    second: &AtomicFact,
) -> Option<(Obj, Obj)> {
    match (first, second) {
        (AtomicFact::LessEqualFact(le), AtomicFact::GreaterEqualFact(ge))
            if objs_same(&le.left, &ge.left) && objs_same(&le.right, &ge.right) =>
        {
            Some((le.left.clone(), le.right.clone()))
        }
        (AtomicFact::GreaterEqualFact(ge), AtomicFact::LessEqualFact(le))
            if objs_same(&le.left, &ge.left) && objs_same(&le.right, &ge.right) =>
        {
            Some((le.left.clone(), le.right.clone()))
        }
        _ => None,
    }
}

// Extract the nonzero-looking factor from `a = 0` / `0 = a`.
pub(super) fn zero_factor_from_equal(eq: &EqualFact) -> Option<&Obj> {
    if is_number_obj(&eq.right, "0") {
        Some(&eq.left)
    } else if is_number_obj(&eq.left, "0") {
        Some(&eq.right)
    } else {
        None
    }
}

// From `a = b` plus `a < b` / `a > b` (or flipped equality), build the covering weak bound.
// Example: equality with less → need `a <= b`; equality with greater → need `a >= b`.
pub(super) fn weak_bound_needed_by_equality_and_strict(
    equality: &AtomicFact,
    strict: &AtomicFact,
) -> Option<AtomicFact> {
    let AtomicFact::EqualFact(eq) = equality else {
        return None;
    };
    match strict {
        AtomicFact::LessFact(l)
            if equal_matches_pair(eq, &l.left, &l.right) =>
        {
            Some(AtomicFact::LessEqualFact(LessEqualFact {
                fact_id: FactId::new(0),
                left: l.left.clone(),
                right: l.right.clone(),
                line_file: l.line_file.clone(),
            }))
        }
        AtomicFact::GreaterFact(g)
            if equal_matches_pair(eq, &g.left, &g.right) =>
        {
            Some(AtomicFact::GreaterEqualFact(GreaterEqualFact {
                fact_id: FactId::new(0),
                left: g.left.clone(),
                right: g.right.clone(),
                line_file: g.line_file.clone(),
            }))
        }
        _ => None,
    }
}

// Match two-branch equality-plus-strict shape; returns (left, right, weak_bound_template).
pub(super) fn match_equality_plus_strict_covers_weak(
    first: &AtomicFact,
    second: &AtomicFact,
) -> Option<(Obj, Obj, AtomicFact)> {
    if let Some(weak) = weak_bound_needed_by_equality_and_strict(first, second) {
        let (left, right) = match (first, second) {
            (AtomicFact::EqualFact(_), AtomicFact::LessFact(l)) => {
                (l.left.clone(), l.right.clone())
            }
            (AtomicFact::EqualFact(_), AtomicFact::GreaterFact(g)) => {
                (g.left.clone(), g.right.clone())
            }
            _ => return None,
        };
        return Some((left, right, weak));
    }
    if let Some(weak) = weak_bound_needed_by_equality_and_strict(second, first) {
        let (left, right) = match (second, first) {
            (AtomicFact::EqualFact(_), AtomicFact::LessFact(l)) => {
                (l.left.clone(), l.right.clone())
            }
            (AtomicFact::EqualFact(_), AtomicFact::GreaterFact(g)) => {
                (g.left.clone(), g.right.clone())
            }
            _ => return None,
        };
        return Some((left, right, weak));
    }
    None
}

fn number_normalized_value(obj: &Obj) -> Option<&str> {
    match obj {
        Obj::Literal(Literal::Number(Number { normalized_value })) => Some(normalized_value.as_str()),
        _ => None,
    }
}

fn nonnegative_integer_literal_to_usize(obj: &Obj) -> Option<usize> {
    let value = number_normalized_value(obj)?.trim();
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

fn positive_integer_literal_to_usize(obj: &Obj) -> Option<usize> {
    let value = nonnegative_integer_literal_to_usize(obj)?;
    if value == 0 {
        None
    } else {
        Some(value)
    }
}

fn mod_subject_modulus_residue(atomic: &AtomicFact) -> Option<(Obj, Obj, Obj)> {
    let AtomicFact::EqualFact(eq) = atomic else {
        return None;
    };
    match (&eq.left, &eq.right) {
        (Obj::IntegerOperator(IntegerOperator::Mod(Mod { left, right })), residue)
            if number_normalized_value(residue).is_some()
                && number_normalized_value(right.as_ref()).is_some() =>
        {
            Some((left.as_ref().clone(), right.as_ref().clone(), residue.clone()))
        }
        (residue, Obj::IntegerOperator(IntegerOperator::Mod(Mod { left, right })))
            if number_normalized_value(residue).is_some()
                && number_normalized_value(right.as_ref()).is_some() =>
        {
            Some((left.as_ref().clone(), right.as_ref().clone(), residue.clone()))
        }
        _ => None,
    }
}

// Pure shape: `n % m = 0 or … or n % m = m-1` for positive literal m, all residues once.
pub(super) fn match_complete_residues(or_branches: &[crate::ast::fact::AndChainAtomicFact]) -> Option<(Obj, Obj)> {
    use crate::ast::fact::AndChainAtomicFact;
    if or_branches.is_empty() {
        return None;
    }
    let AndChainAtomicFact::AtomicFact(first_atomic) = &or_branches[0] else {
        return None;
    };
    let Some((first_subject, first_modulus, first_residue)) = mod_subject_modulus_residue(first_atomic) else {
        return None;
    };
    let Some(modulus_value) = positive_integer_literal_to_usize(&first_modulus) else {
        return None;
    };
    if modulus_value <= 1 || modulus_value != or_branches.len() {
        return None;
    }
    let mut seen = vec![false; modulus_value];
    let first_residue_value = nonnegative_integer_literal_to_usize(&first_residue)?;
    if first_residue_value >= modulus_value {
        return None;
    }
    seen[first_residue_value] = true;
    for branch in or_branches.iter().skip(1) {
        let AndChainAtomicFact::AtomicFact(atomic) = branch else {
            return None;
        };
        let (subject, modulus, residue) = mod_subject_modulus_residue(atomic)?;
        if !objs_same(&subject, &first_subject) || !objs_same(&modulus, &first_modulus) {
            return None;
        }
        let residue_value = nonnegative_integer_literal_to_usize(&residue)?;
        if residue_value >= modulus_value || seen[residue_value] {
            return None;
        }
        seen[residue_value] = true;
    }
    if seen.iter().all(|s| *s) {
        Some((first_subject, first_modulus))
    } else {
        None
    }
}

fn integer_literal_i128(obj: &Obj) -> Option<i128> {
    number_normalized_value(obj)?.parse::<i128>().ok()
}

fn integer_successor_value(base: &Obj, offset: usize) -> Obj {
    if offset == 0 {
        return base.clone();
    }
    if let Some(base_value) = integer_literal_i128(base) {
        return Obj::Literal(Literal::Number(Number {
            normalized_value: (base_value + offset as i128).to_string(),
        }));
    }
    Obj::ArithmeticOperator(ArithmeticOperator::Add(Add {
        left: Box::new(base.clone()),
        right: Box::new(Obj::Literal(Literal::Number(Number {
            normalized_value: offset.to_string(),
        }))),
    }))
}

fn equality_branch_matches_subject_value(atomic: &AtomicFact, subject: &Obj, value: &Obj) -> bool {
    let AtomicFact::EqualFact(eq) = atomic else {
        return false;
    };
    equal_matches_pair(eq, subject, value)
}

fn strict_tail_matches_subject_value(atomic: &AtomicFact, subject: &Obj, tail_value: &Obj) -> bool {
    match atomic {
        AtomicFact::GreaterFact(g) => {
            objs_same(&g.left, subject) && objs_same(&g.right, tail_value)
        }
        AtomicFact::LessFact(l) => {
            objs_same(&l.right, subject) && objs_same(&l.left, tail_value)
        }
        _ => false,
    }
}

fn integer_successor_tail_with_subject_base(
    or_branches: &[crate::ast::fact::AndChainAtomicFact],
    subject: &Obj,
    base: &Obj,
) -> bool {
    use crate::ast::fact::AndChainAtomicFact;
    let equality_count = or_branches.len() - 1;
    for (offset, fact) in or_branches.iter().take(equality_count).enumerate() {
        let AndChainAtomicFact::AtomicFact(atomic) = fact else {
            return false;
        };
        let value = integer_successor_value(base, offset);
        if !equality_branch_matches_subject_value(atomic, subject, &value) {
            return false;
        }
    }
    let tail_value = integer_successor_value(base, equality_count - 1);
    let AndChainAtomicFact::AtomicFact(last_atomic) = &or_branches[equality_count] else {
        return false;
    };
    strict_tail_matches_subject_value(last_atomic, subject, &tail_value)
}

// Match `x = base or x = base+1 or … or x > last` (or `<` flipped tail).
pub(super) fn match_integer_successor_tail(
    or_branches: &[crate::ast::fact::AndChainAtomicFact],
) -> Option<(Obj, Obj)> {
    use crate::ast::fact::AndChainAtomicFact;
    if or_branches.len() < 2 {
        return None;
    }
    let AndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(first_eq)) = &or_branches[0] else {
        return None;
    };
    for (subject, base) in [
        (first_eq.left.clone(), first_eq.right.clone()),
        (first_eq.right.clone(), first_eq.left.clone()),
    ] {
        if integer_successor_tail_with_subject_base(or_branches, &subject, &base) {
            return Some((subject, base));
        }
    }
    None
}

fn nonzero_operand_from_not_equal(atomic: &AtomicFact) -> Option<Obj> {
    let AtomicFact::NotEqualFact(ne) = atomic else {
        return None;
    };
    if is_number_obj(&ne.right, "0") {
        Some(ne.left.clone())
    } else if is_number_obj(&ne.left, "0") {
        Some(ne.right.clone())
    } else {
        None
    }
}

// Match `a != 0 or b != 0`; returns the two bases.
pub(super) fn match_component_nonzero_pair(
    first: &AtomicFact,
    second: &AtomicFact,
) -> Option<(Obj, Obj)> {
    let left = nonzero_operand_from_not_equal(first)?;
    let right = nonzero_operand_from_not_equal(second)?;
    Some((left, right))
}

fn add_obj(left: &Obj, right: &Obj) -> Obj {
    Obj::ArithmeticOperator(ArithmeticOperator::Add(Add {
        left: Box::new(left.clone()),
        right: Box::new(right.clone()),
    }))
}

fn pow_obj(base: &Obj, exponent: &Obj) -> Obj {
    Obj::ArithmeticOperator(ArithmeticOperator::Pow(Pow {
        base: Box::new(base.clone()),
        exponent: Box::new(exponent.clone()),
    }))
}

fn two_obj() -> Obj {
    Obj::Literal(Literal::Number(Number {
        normalized_value: "2".into(),
    }))
}

// Candidate known facts: a^2+b^2 != 0 and a*a+b*b != 0 (both orders).
pub(super) fn square_sum_nonzero_candidates(left: &Obj, right: &Obj) -> Vec<AtomicFact> {
    let zero = zero_obj();
    let two = two_obj();
    let mut out = Vec::new();
    for (a, b) in [(left, right), (right, left)] {
        let pow_sum = add_obj(&pow_obj(a, &two), &pow_obj(b, &two));
        out.push(AtomicFact::NotEqualFact(NotEqualFact {
            fact_id: FactId::new(0),
            left: pow_sum,
            right: zero.clone(),
            line_file: None,
        }));
        let mul_sum = add_obj(&mul_obj(a, a), &mul_obj(b, b));
        out.push(AtomicFact::NotEqualFact(NotEqualFact {
            fact_id: FactId::new(0),
            left: mul_sum,
            right: zero.clone(),
            line_file: None,
        }));
    }
    out
}

fn obj_plus_one_base(obj: &Obj) -> Option<Obj> {
    let Obj::ArithmeticOperator(ArithmeticOperator::Add(Add { left, right })) = obj else {
        return None;
    };
    if is_number_obj(right.as_ref(), "1") {
        return Some(left.as_ref().clone());
    }
    if is_number_obj(left.as_ref(), "1") {
        return Some(right.as_ref().clone());
    }
    None
}

fn obj_minus_one_base(obj: &Obj) -> Option<Obj> {
    let Obj::ArithmeticOperator(ArithmeticOperator::Sub(Sub { left, right })) = obj else {
        return None;
    };
    if is_number_obj(right.as_ref(), "1") {
        Some(left.as_ref().clone())
    } else {
        None
    }
}

// Normalize weak order to (smaller_side_subject_view): <= keeps (L,R); >= flips to (R,L).
fn weak_order_oriented(fact: &AtomicFact) -> Option<(Obj, Obj)> {
    match fact {
        AtomicFact::LessEqualFact(f) => Some((f.left.clone(), f.right.clone())),
        AtomicFact::GreaterEqualFact(f) => Some((f.right.clone(), f.left.clone())),
        _ => None,
    }
}

// Match `x <= n or x >= n + 1` (either branch order).
pub(super) fn match_integer_discrete_successor_split(
    first: &AtomicFact,
    second: &AtomicFact,
) -> Option<(Obj, Obj)> {
    let (subject, base) = weak_order_oriented(first)?;
    let (successor, successor_subject) = weak_order_oriented(second)?;
    let successor_base = obj_plus_one_base(&successor)?;
    if objs_same(&subject, &successor_subject) && objs_same(&base, &successor_base) {
        Some((subject, base))
    } else {
        None
    }
}

// Match `x >= n or x <= n - 1` (either branch order).
pub(super) fn match_integer_discrete_predecessor_split(
    first: &AtomicFact,
    second: &AtomicFact,
) -> Option<(Obj, Obj)> {
    let (base, subject) = weak_order_oriented(first)?;
    let (predecessor_subject, predecessor) = weak_order_oriented(second)?;
    let predecessor_base = obj_minus_one_base(&predecessor)?;
    if objs_same(&subject, &predecessor_subject) && objs_same(&base, &predecessor_base) {
        Some((subject, base))
    } else {
        None
    }
}

pub(super) fn match_integer_discrete_split(
    first: &AtomicFact,
    second: &AtomicFact,
) -> Option<(Obj, Obj)> {
    match_integer_discrete_successor_split(first, second)
        .or_else(|| match_integer_discrete_successor_split(second, first))
        .or_else(|| match_integer_discrete_predecessor_split(first, second))
        .or_else(|| match_integer_discrete_predecessor_split(second, first))
}

fn zero_obj() -> Obj {
    Obj::Literal(Literal::Number(Number {
        normalized_value: "0".into(),
    }))
}

fn mul_obj(left: &Obj, right: &Obj) -> Obj {
    Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul {
        left: Box::new(left.clone()),
        right: Box::new(right.clone()),
    }))
}

impl Runtime {
    // Prove `left $in R` and `right $in R`. Soft miss either side → None.
    pub(super) fn prove_both_objs_in_r(
        &mut self,
        left: &Obj,
        right: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<(VerifyFactResult, VerifyFactResult)>> {
        let left_fact_id = self.global_ids.allocate_fact_id();
        let left_in_r = self.verify_fact(
            &Fact::AtomicFact(AtomicFact::InFact(InFact {
                fact_id: left_fact_id,
                element: left.clone(),
                set: Obj::StandardSet(StandardSet::R),
                line_file: None,
            })),
            verify_state.clone(),
        )?;
        if left_in_r.is_failed() {
            return Ok(None);
        }
        let right_fact_id = self.global_ids.allocate_fact_id();
        let right_in_r = self.verify_fact(
            &Fact::AtomicFact(AtomicFact::InFact(InFact {
                fact_id: right_fact_id,
                element: right.clone(),
                set: Obj::StandardSet(StandardSet::R),
                line_file: None,
            })),
            verify_state,
        )?;
        if right_in_r.is_failed() {
            return Ok(None);
        }
        Ok(Some((left_in_r, right_in_r)))
    }

    // Prove `left $in Z` and `right $in Z`. Soft miss either side → None.
    pub(super) fn prove_both_objs_in_z(
        &mut self,
        left: &Obj,
        right: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<(VerifyFactResult, VerifyFactResult)>> {
        let left_fact_id = self.global_ids.allocate_fact_id();
        let left_in_z = self.verify_fact(
            &Fact::AtomicFact(AtomicFact::InFact(InFact {
                fact_id: left_fact_id,
                element: left.clone(),
                set: Obj::StandardSet(StandardSet::Z),
                line_file: None,
            })),
            verify_state.clone(),
        )?;
        if left_in_z.is_failed() {
            return Ok(None);
        }
        let right_fact_id = self.global_ids.allocate_fact_id();
        let right_in_z = self.verify_fact(
            &Fact::AtomicFact(AtomicFact::InFact(InFact {
                fact_id: right_fact_id,
                element: right.clone(),
                set: Obj::StandardSet(StandardSet::Z),
                line_file: None,
            })),
            verify_state,
        )?;
        if right_in_z.is_failed() {
            return Ok(None);
        }
        Ok(Some((left_in_z, right_in_z)))
    }

    // Prove known `a * b = 0` or `b * a = 0`. Soft miss both → None.
    pub(super) fn prove_product_is_zero(
        &mut self,
        left: &Obj,
        right: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<VerifyFactResult>> {
        for (a, b) in [(left, right), (right, left)] {
            let fact_id = self.global_ids.allocate_fact_id();
            let product_zero = self.verify_fact(
                &Fact::AtomicFact(AtomicFact::EqualFact(EqualFact {
                    fact_id,
                    left: mul_obj(a, b),
                    right: zero_obj(),
                    line_file: None,
                })),
                verify_state.clone(),
            )?;
            if !product_zero.is_failed() {
                return Ok(Some(product_zero));
            }
        }
        Ok(None)
    }
}
