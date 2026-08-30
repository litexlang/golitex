//! Conjunction, disjunction, and associated proof-term rendering.

use super::super::*;

pub(in super::super) fn conjunction(facts: &[String]) -> String {
    match facts {
        [] => "True".to_string(),
        [only] => only.clone(),
        // A retained conclusion can itself be an `AndFact` or relation
        // chain. Preserve that Result boundary: the proof compiler publishes
        // one proof term for each outer conclusion and projects its inner
        // components separately. Without parentheses Lean reassociates the
        // nested conjunction and changes the type expected at that slot.
        _ => facts
            .iter()
            .map(|fact| format!("({fact})"))
            .collect::<Vec<_>>()
            .join(" ∧ "),
    }
}

pub(in super::super) fn conjunction_components(fact: &Fact) -> Result<Vec<Fact>, String> {
    match fact {
        Fact::AndFact(and_fact) => Ok(and_fact.facts.iter().cloned().map(Fact::from).collect()),
        Fact::ChainFact(chain_fact) => chain_fact
            .facts()
            .map(|facts| facts.into_iter().map(Fact::from).collect())
            .map_err(|error| format!("invalid retained relation chain: {error:?}")),
        _ => Err(format!(
            "expected conjunction or relation chain, found `{fact}`"
        )),
    }
}

pub(in super::super) fn disjunction_components(fact: &Fact) -> Result<Vec<Fact>, String> {
    let Fact::OrFact(or_fact) = fact else {
        return Err(format!("expected disjunction, found `{fact}`"));
    };
    Ok(or_fact.facts.iter().cloned().map(Fact::from).collect())
}

pub(in super::super) fn right_associated_conjunction_proof(
    proofs: &[String],
) -> Result<String, String> {
    let Some(last) = proofs.last() else {
        return Err("conjunction introduction retained no component proofs".into());
    };
    let mut result = last.clone();
    for proof in proofs[..proofs.len() - 1].iter().rev() {
        result = format!("⟨{proof}, {result}⟩");
    }
    Ok(result)
}

pub(in super::super) fn right_associated_disjunction_injection(
    proof: String,
    selected_index: usize,
    count: usize,
) -> Result<String, String> {
    if count == 0 || selected_index >= count {
        return Err("disjunction introduction selected an out-of-range branch".into());
    }
    if count == 1 {
        return Ok(proof);
    }
    let mut result = if selected_index + 1 < count {
        format!("Or.inl ({proof})")
    } else {
        proof
    };
    for _ in 0..selected_index {
        result = format!("Or.inr ({result})");
    }
    Ok(result)
}

pub(in super::super) fn conjunction_projection(
    source: &str,
    index: usize,
    count: usize,
) -> Result<String, String> {
    if count == 0 || index >= count {
        return Err("conjunction projection selected an out-of-range component".into());
    }
    if count == 1 {
        return Ok(source.to_string());
    }
    let mut projection = source.to_string();
    for _ in 0..index {
        projection.push_str(".2");
    }
    if index + 1 < count {
        projection.push_str(".1");
    }
    Ok(projection)
}
