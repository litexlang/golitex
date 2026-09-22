use crate::new_pipeline::ast::fact::{AtomicFact, ExistShapedFact, QuantifierFreeFact};
use crate::new_pipeline::ast::obj::{IdentifierObj, Obj, StandardSet, Literal};
use crate::new_pipeline::ast::param::ParamType;
use crate::new_pipeline::runtime::runtime_ids::IdentifierId;

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

fn flatten_real_param_ids(
    groups: &[crate::new_pipeline::ast::param::TypedParameterGroup],
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
