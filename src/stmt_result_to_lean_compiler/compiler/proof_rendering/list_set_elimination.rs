//! Finite list-set membership elimination.

use super::super::*;

/// Literal-set membership carries only an observation-free representation
/// equality. The equality alternatives inferred from that membership must
/// state the same proposition explicitly; Lean's default observer for a
/// numeric literal would otherwise make `x = 1` stronger than the source
/// membership can justify.
pub(in super::super) fn render_no_observation_equality_alternatives_fact(
    target: &Fact,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    match target {
        Fact::AtomicFact(AtomicFact::EqualFact(equality)) => Ok(format!(
            "@Litex.Same _ _ (Litex.ComplexObserver.none _) (Litex.ComplexObserver.none _) {} {}",
            render_obj(&equality.left, context)?,
            render_obj(&equality.right, context)?
        )),
        Fact::OrFact(_) => {
            let branches = disjunction_components(target)?;
            if branches.is_empty() {
                return Err("literal-set equality alternatives retained no branches".into());
            }
            Ok(branches
                .iter()
                .map(|branch| render_no_observation_equality_alternatives_fact(branch, context))
                .collect::<Result<Vec<_>, _>>()?
                .join(" ∨ "))
        }
        _ => Err(format!(
            "literal-set membership inference retained non-equality alternatives `{target}`"
        )),
    }
}

pub(in super::super) fn render_list_set_membership_elimination_from_fact_and_proof(
    target: &Fact,
    source_membership: &Fact,
    source_proof: &str,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    let (element, set) = membership_parts(source_membership)?;
    let Obj::ListSet(list_set) = set else {
        return Err("list-set membership elimination cites another set constructor".into());
    };
    if list_set.list.is_empty() {
        return Err("empty list-set membership cannot produce an equality branch".into());
    }
    let target_components = if list_set.list.len() == 1 {
        vec![target.clone()]
    } else {
        disjunction_components(target)?
    };
    if target_components.len() != list_set.list.len() {
        return Err("list-set membership inference changed its branch count".into());
    }
    for (component, item) in target_components.iter().zip(list_set.list.iter()) {
        let (left, right) = equality_parts(component)?;
        if obj_equality_key(left) != obj_equality_key(element)
            || obj_equality_key(right) != obj_equality_key(item.as_ref())
        {
            return Err(
                "list-set membership inference changed its ordered equality branches".into(),
            );
        }
    }
    render_no_observation_equality_alternatives_fact(target, context)?;
    let item_terms = list_set
        .list
        .iter()
        .map(|item| render_obj(item.as_ref(), context))
        .collect::<Result<Vec<_>, _>>()?;
    let mut lines = vec![
        "(by".to_string(),
        format!("  rcases ({source_proof}) with ⟨__member, __same⟩"),
    ];
    render_list_set_elimination_cases(&item_terms, 0, "__member", "  ", &mut lines);
    lines.push(")".into());
    Ok(lines.join("\n"))
}

pub(in super::super) fn render_list_set_elimination_cases(
    item_terms: &[String],
    index: usize,
    member: &str,
    indent: &str,
    lines: &mut Vec<String>,
) {
    let head = format!("__head{index}");
    let tail = format!("__tail{index}");
    lines.push(format!("{indent}cases {member} with"));
    lines.push(format!("{indent}| inl {head} =>"));
    lines.push(format!("{indent}  cases {head}"));
    let (_, representation) = render_list_set_representation_bridge(&item_terms[index], index);
    let equality = format!(
        "Litex.Same.transNoObservation __same (Litex.Same.symmNoObservation ({representation}))"
    );
    lines.push(format!(
        "{indent}  exact {}",
        inject_disjunction_branch(equality, index, item_terms.len())
    ));
    lines.push(format!("{indent}| inr {tail} =>"));
    if index + 1 == item_terms.len() {
        lines.push(format!("{indent}  exact PEmpty.elim {tail}"));
    } else {
        render_list_set_elimination_cases(
            item_terms,
            index + 1,
            &tail,
            &format!("{indent}  "),
            lines,
        );
    }
}

pub(in super::super) fn inject_disjunction_branch(
    mut proof: String,
    selected_index: usize,
    branch_count: usize,
) -> String {
    if branch_count == 1 {
        return proof;
    }
    if selected_index + 1 < branch_count {
        proof = format!("Or.inl ({proof})");
    }
    for _ in 0..selected_index {
        proof = format!("Or.inr ({proof})");
    }
    proof
}

pub(in super::super) fn render_list_set_representation_bridge(
    selected_term: &str,
    selected_index: usize,
) -> (String, String) {
    let mut witness = "Litex.SingletonCarrier.element".to_string();
    let mut representation = format!("Litex.Same.singletonNoObservation {selected_term}");
    representation = format!(
        "Litex.Same.transNoObservation ({representation}) (Litex.Same.sumLeftNoObservation ({witness}))"
    );
    witness = format!("Sum.inl ({witness})");
    for _ in 0..selected_index {
        representation = format!(
            "Litex.Same.transNoObservation ({representation}) (Litex.Same.sumRightNoObservation ({witness}))"
        );
        witness = format!("Sum.inr ({witness})");
    }
    (witness, representation)
}
