use std::collections::HashSet;

use crate::ast::fact::{
    AtomicFact, ChainFact, ExistShapedFact, PlainExistFact, QuantifierFreeFact,
};
use crate::ast::names::AtomicName;
use crate::ast::obj::{ArithmeticOperator, IdentifierObj, Literal, Number, Obj, StandardSet};
use crate::ast::param::ParamType;
use crate::instantiate::collect_free_plain_ids;
use crate::parse::keywords::LESS;
use crate::runtime::runtime_ids::IdentifierId;

// Soft match: plain exist over 1–2 real binders with a single comparison atom.
// Returns free (non-witness) operands that must be known reals.
pub(super) fn real_line_comparison_free_operands(exist_fact: &ExistShapedFact) -> Option<Vec<Obj>> {
    let ExistShapedFact::Exist(plain) = exist_fact else {
        return None;
    };
    if plain.facts.len() != 1 {
        return None;
    }
    let param_ids = flatten_real_param_ids(&plain.typed_parameters.groups)?;
    if param_ids.is_empty() || param_ids.len() > 2 {
        return None;
    }

    let QuantifierFreeFact::AtomicFact(atomic) = &plain.facts[0] else {
        return None;
    };
    let (left, right) = comparison_sides(atomic)?;

    if param_ids.len() == 1 {
        let witness_id = param_ids[0];
        let other = if plain_id(left) == Some(witness_id) {
            right
        } else if plain_id(right) == Some(witness_id) {
            left
        } else {
            return None;
        };
        if obj_mentions_id(other, witness_id) {
            return None;
        }
        return Some(vec![other.clone()]);
    }

    let (Some(left_id), Some(right_id)) = (plain_id(left), plain_id(right)) else {
        return None;
    };
    if left_id == right_id {
        return None;
    }
    if !param_ids.contains(&left_id) || !param_ids.contains(&right_id) {
        return None;
    }
    Some(vec![])
}

// Soft match: `exist x S st {x = a}` or `{a = x}` with free `a`.
// Returns `(S, a)`.
pub(super) fn equality_witness_from_membership_parts(
    exist_fact: &ExistShapedFact,
) -> Option<(Obj, Obj)> {
    let ExistShapedFact::Exist(plain) = exist_fact else {
        return None;
    };
    if plain.facts.len() != 1 {
        return None;
    }
    let (witness_id, set) = single_obj_param(plain)?;
    let QuantifierFreeFact::AtomicFact(AtomicFact::EqualFact(equal)) = &plain.facts[0] else {
        return None;
    };
    let free = if plain_id(&equal.left) == Some(witness_id) {
        if obj_mentions_id(&equal.right, witness_id) {
            return None;
        }
        equal.right.clone()
    } else if plain_id(&equal.right) == Some(witness_id) {
        if obj_mentions_id(&equal.left, witness_id) {
            return None;
        }
        equal.left.clone()
    } else {
        return None;
    };
    Some((set, free))
}

// Soft match: `exist x S st {x $in S}` with the same set on the binder and atom.
pub(super) fn nonempty_set_member_witness_set(exist_fact: &ExistShapedFact) -> Option<Obj> {
    let ExistShapedFact::Exist(plain) = exist_fact else {
        return None;
    };
    if plain.facts.len() != 1 {
        return None;
    }
    let (witness_id, set) = single_obj_param(plain)?;
    let QuantifierFreeFact::AtomicFact(AtomicFact::InFact(in_fact)) = &plain.facts[0] else {
        return None;
    };
    if plain_id(&in_fact.element) != Some(witness_id) {
        return None;
    }
    if in_fact.set.ir() != set.ir() {
        return None;
    }
    Some(set)
}

fn single_obj_param(plain: &PlainExistFact) -> Option<(IdentifierId, Obj)> {
    let mut ids = Vec::new();
    let mut set = None;
    for group in &plain.typed_parameters.groups {
        let ParamType::Obj(domain) = &group.param_type else {
            return None;
        };
        match &set {
            None => set = Some(domain.clone()),
            Some(existing) if existing.ir() == domain.ir() => {}
            _ => return None,
        }
        for param in &group.params {
            ids.push(param.id);
        }
    }
    if ids.len() != 1 {
        return None;
    }
    Some((ids[0], set?))
}

fn flatten_real_param_ids(
    groups: &[crate::ast::param::TypedParameterGroup],
) -> Option<Vec<IdentifierId>> {
    let mut ids = Vec::new();
    for group in groups {
        match &group.param_type {
            ParamType::Obj(Obj::StandardSet(StandardSet::R)) => {}
            _ => return None,
        }
        for param in &group.params {
            ids.push(param.id);
        }
    }
    Some(ids)
}

fn comparison_sides(atomic: &AtomicFact) -> Option<(&Obj, &Obj)> {
    match atomic {
        AtomicFact::EqualFact(f) => Some((&f.left, &f.right)),
        AtomicFact::NotEqualFact(f) => Some((&f.left, &f.right)),
        AtomicFact::LessFact(f) => Some((&f.left, &f.right)),
        AtomicFact::GreaterFact(f) => Some((&f.left, &f.right)),
        AtomicFact::LessEqualFact(f) => Some((&f.left, &f.right)),
        AtomicFact::GreaterEqualFact(f) => Some((&f.left, &f.right)),
        _ => None,
    }
}

fn plain_id(obj: &Obj) -> Option<IdentifierId> {
    match obj {
        Obj::Identifier(IdentifierObj::Plain { id, .. }) => Some(*id),
        _ => None,
    }
}

// Soft miss if the free side can mention the witness. Numbers and other plain
// identifiers are allowed; richer shapes are rejected (conservative).
fn obj_mentions_id(obj: &Obj, id: IdentifierId) -> bool {
    match obj {
        Obj::Identifier(IdentifierObj::Plain { id: plain, .. }) => *plain == id,
        Obj::Literal(Literal::Number(_))
        | Obj::StandardSet(_)
        | Obj::Literal(Literal::Pi(_))
        | Obj::Literal(Literal::EulerNumber(_))
        | Obj::Literal(Literal::ImaginaryUnit(_)) => false,
        _ => true,
    }
}

// True when `obj` free-mentions any of the given binder ids.
fn obj_depends_on_ids(obj: &Obj, ids: &[IdentifierId]) -> bool {
    let mut free = HashSet::new();
    collect_free_plain_ids(obj, &HashSet::new(), &mut free);
    ids.iter().any(|id| free.contains(id))
}

fn flatten_obj_param_bindings(plain: &PlainExistFact) -> Option<Vec<(IdentifierId, Obj)>> {
    let mut out = Vec::new();
    for group in &plain.typed_parameters.groups {
        let ParamType::Obj(domain) = &group.param_type else {
            return None;
        };
        for param in &group.params {
            out.push((param.id, domain.clone()));
        }
    }
    Some(out)
}

fn is_zero_literal(obj: &Obj) -> bool {
    matches!(
        obj,
        Obj::Literal(Literal::Number(Number { normalized_value })) if normalized_value == "0"
    )
}

fn is_one_literal(obj: &Obj) -> bool {
    matches!(
        obj,
        Obj::Literal(Literal::Number(Number { normalized_value })) if normalized_value == "1"
    )
}

fn is_plain_id(obj: &Obj, id: IdentifierId) -> bool {
    plain_id(obj) == Some(id)
}

fn is_less_prop(name: &AtomicName) -> bool {
    matches!(name, AtomicName::Plain { name } if name == LESS)
}

// Soft match: `exist a, b Z st {b > 0, q = a / b}` (or `0 < b`).
// Returns free rational `q`.
// Note: exist-body WD of `a / b` currently fails unless `b != 0` is known from
// the binder (sibling `b > 0` is not assumed during WD), so green tracers may
// need the Z* ratio form instead.
pub(super) fn rational_positive_denominator_free_operand(
    exist_fact: &ExistShapedFact,
) -> Option<Obj> {
    let ExistShapedFact::Exist(plain) = exist_fact else {
        return None;
    };
    if plain.facts.len() != 2 {
        return None;
    }
    let bindings = flatten_obj_param_bindings(plain)?;
    if bindings.len() != 2 {
        return None;
    }
    let (num_id, num_set) = &bindings[0];
    let (den_id, den_set) = &bindings[1];
    if !matches!(num_set, Obj::StandardSet(StandardSet::Z))
        || !matches!(den_set, Obj::StandardSet(StandardSet::Z))
    {
        return None;
    }
    let witness_ids = [*num_id, *den_id];

    let denominator_is_positive = plain.facts.iter().any(|fact| match fact {
        QuantifierFreeFact::AtomicFact(AtomicFact::GreaterFact(g)) => {
            is_plain_id(&g.left, *den_id) && is_zero_literal(&g.right)
        }
        QuantifierFreeFact::AtomicFact(AtomicFact::LessFact(l)) => {
            is_zero_literal(&l.left) && is_plain_id(&l.right, *den_id)
        }
        _ => false,
    });
    if !denominator_is_positive {
        return None;
    }

    let ratio_other = plain.facts.iter().find_map(|fact| {
        let QuantifierFreeFact::AtomicFact(AtomicFact::EqualFact(equal)) = fact else {
            return None;
        };
        let is_ratio = |obj: &Obj| match obj {
            Obj::ArithmeticOperator(ArithmeticOperator::Div(div)) => {
                is_plain_id(div.left.as_ref(), *num_id) && is_plain_id(div.right.as_ref(), *den_id)
            }
            _ => false,
        };
        if is_ratio(&equal.left) {
            Some(equal.right.clone())
        } else if is_ratio(&equal.right) {
            Some(equal.left.clone())
        } else {
            None
        }
    })?;
    if obj_depends_on_ids(&ratio_other, &witness_ids) {
        return None;
    }
    Some(ratio_other)
}

// Soft match: `exist a Z, b Z* st {q = a / b}`.
// Returns free rational `q`.
pub(super) fn rational_integer_ratio_free_operand(exist_fact: &ExistShapedFact) -> Option<Obj> {
    let ExistShapedFact::Exist(plain) = exist_fact else {
        return None;
    };
    if plain.facts.len() != 1 {
        return None;
    }
    let bindings = flatten_obj_param_bindings(plain)?;
    if bindings.len() != 2 {
        return None;
    }
    let (num_id, num_set) = &bindings[0];
    let (den_id, den_set) = &bindings[1];
    if !matches!(num_set, Obj::StandardSet(StandardSet::Z))
        || !matches!(den_set, Obj::StandardSet(StandardSet::ZStar))
    {
        return None;
    }
    let witness_ids = [*num_id, *den_id];
    let QuantifierFreeFact::AtomicFact(AtomicFact::EqualFact(equal)) = &plain.facts[0] else {
        return None;
    };
    let is_ratio = |obj: &Obj| match obj {
        Obj::ArithmeticOperator(ArithmeticOperator::Div(div)) => {
            is_plain_id(div.left.as_ref(), *num_id) && is_plain_id(div.right.as_ref(), *den_id)
        }
        _ => false,
    };
    let other = if is_ratio(&equal.left) {
        equal.right.clone()
    } else if is_ratio(&equal.right) {
        equal.left.clone()
    } else {
        return None;
    };
    if obj_depends_on_ids(&other, &witness_ids) {
        return None;
    }
    Some(other)
}

// Soft match: `exist k Z st {a = b * k}` (either product order / equality side).
// Returns `(a, b)`.
pub(super) fn integer_multiple_from_zero_remainder_operands(
    exist_fact: &ExistShapedFact,
) -> Option<(Obj, Obj)> {
    let ExistShapedFact::Exist(plain) = exist_fact else {
        return None;
    };
    if plain.facts.len() != 1 {
        return None;
    }
    let (witness_id, set) = single_obj_param(plain)?;
    if !matches!(set, Obj::StandardSet(StandardSet::Z)) {
        return None;
    }
    let QuantifierFreeFact::AtomicFact(AtomicFact::EqualFact(equal)) = &plain.facts[0] else {
        return None;
    };
    let extract_divisor = |candidate: &Obj| match candidate {
        Obj::ArithmeticOperator(ArithmeticOperator::Mul(product))
            if is_plain_id(product.left.as_ref(), witness_id) =>
        {
            Some(product.right.as_ref().clone())
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Mul(product))
            if is_plain_id(product.right.as_ref(), witness_id) =>
        {
            Some(product.left.as_ref().clone())
        }
        _ => None,
    };
    let (dividend, divisor) = if let Some(divisor) = extract_divisor(&equal.right) {
        (equal.left.clone(), divisor)
    } else if let Some(divisor) = extract_divisor(&equal.left) {
        (equal.right.clone(), divisor)
    } else {
        return None;
    };
    let witness_ids = [witness_id];
    if obj_depends_on_ids(&dividend, &witness_ids) || obj_depends_on_ids(&divisor, &witness_ids) {
        return None;
    }
    Some((dividend, divisor))
}

// Soft match: `exist n N+ st {1 / n < epsilon}`.
// Returns free positive bound `epsilon`.
pub(super) fn archimedean_reciprocal_bound(exist_fact: &ExistShapedFact) -> Option<Obj> {
    let ExistShapedFact::Exist(plain) = exist_fact else {
        return None;
    };
    if plain.facts.len() != 1 {
        return None;
    }
    let (witness_id, set) = single_obj_param(plain)?;
    if !matches!(set, Obj::StandardSet(StandardSet::NPos)) {
        return None;
    }
    let QuantifierFreeFact::AtomicFact(AtomicFact::LessFact(less)) = &plain.facts[0] else {
        return None;
    };
    let Obj::ArithmeticOperator(ArithmeticOperator::Div(div)) = &less.left else {
        return None;
    };
    if !is_one_literal(div.left.as_ref()) || !is_plain_id(div.right.as_ref(), witness_id) {
        return None;
    }
    if obj_depends_on_ids(&less.right, &[witness_id]) {
        return None;
    }
    Some(less.right.clone())
}

// Soft match: `exist r R st {a < r < b}` as a three-object strict chain.
// Returns free endpoints `(a, b)`.
pub(super) fn real_density_midpoint_endpoints(exist_fact: &ExistShapedFact) -> Option<(Obj, Obj)> {
    dense_order_exist_endpoints(exist_fact, StandardSet::R)
}

fn dense_order_exist_endpoints(
    exist_fact: &ExistShapedFact,
    witness_carrier: StandardSet,
) -> Option<(Obj, Obj)> {
    let ExistShapedFact::Exist(plain) = exist_fact else {
        return None;
    };
    if plain.facts.len() != 1 {
        return None;
    }
    let (witness_id, set) = single_obj_param(plain)?;
    let Obj::StandardSet(carrier) = set else {
        return None;
    };
    let carrier_ok = matches!(
        (carrier, witness_carrier),
        (StandardSet::R, StandardSet::R) | (StandardSet::Q, StandardSet::Q)
    );
    if !carrier_ok {
        return None;
    }
    let QuantifierFreeFact::ChainFact(chain) = &plain.facts[0] else {
        return None;
    };
    let (left, right) = strict_between_chain_endpoints(chain, witness_id)?;
    if obj_depends_on_ids(&left, &[witness_id]) || obj_depends_on_ids(&right, &[witness_id]) {
        return None;
    }
    Some((left, right))
}

fn strict_between_chain_endpoints(
    chain: &ChainFact,
    witness_id: IdentifierId,
) -> Option<(Obj, Obj)> {
    if chain.objs.len() != 3 || chain.prop_names.len() != 2 {
        return None;
    }
    if !is_less_prop(&chain.prop_names[0]) || !is_less_prop(&chain.prop_names[1]) {
        return None;
    }
    if !is_plain_id(&chain.objs[1], witness_id) {
        return None;
    }
    Some((chain.objs[0].clone(), chain.objs[2].clone()))
}
