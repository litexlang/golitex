use super::negate_fact_for_contra::as_quantifier_free;
use crate::ast::fact::{Fact, ForallFactWithIff, PlainExistFact, QuantifierFreeFact};
use crate::ast::line_file::SourceLine;
use crate::runtime::Runtime;

// not forall x, D => (P iff Q) is exist x, D and
// (not P or not Q) and (P or Q). Conjunction bodies preserve the compact
// existing shapes; there is no need to expand the equivalence into one DNF.
pub(super) fn negate_forall_iff(
    runtime: &mut Runtime,
    iff: &ForallFactWithIff,
) -> Result<Fact, String> {
    let mut dom = Vec::new();
    for fact in &iff.forall_fact.dom_facts {
        dom.push(as_quantifier_free(fact).ok_or_else(|| {
            "by contra: existential counterexample cannot represent a quantified iff domain"
                .to_string()
        })?);
    }
    let mut left = Vec::new();
    let mut right = Vec::new();
    for fact in &iff.forall_fact.then_facts {
        left.push(as_quantifier_free(&fact.clone().into()).ok_or_else(|| {
            "by contra: existential counterexample cannot represent an existential iff clause"
                .to_string()
        })?);
    }
    for fact in &iff.iff_facts {
        right.push(as_quantifier_free(&fact.clone().into()).ok_or_else(|| {
            "by contra: existential counterexample cannot represent an existential iff clause"
                .to_string()
        })?);
    }
    let line = iff.line_file.clone();
    let not_left = runtime
        .negate_quantifier_free_conjunction_to_conjuncts(&left, line.clone())
        .map_err(|e| format!("by contra: cannot negate iff left side: {e:?}"))?
        .ok_or_else(|| "by contra: empty iff left side".to_string())?;
    let not_right = runtime
        .negate_quantifier_free_conjunction_to_conjuncts(&right, line.clone())
        .map_err(|e| format!("by contra: cannot negate iff right side: {e:?}"))?
        .ok_or_else(|| "by contra: empty iff right side".to_string())?;
    dom.extend(disjoin_conjunctions(
        runtime,
        &not_left,
        &not_right,
        line.clone(),
    )?);
    dom.extend(disjoin_conjunctions(runtime, &left, &right, line.clone())?);
    Ok(Fact::ExistFact(PlainExistFact {
        fact_id: runtime.global_ids.allocate_fact_id(),
        typed_parameters: iff.forall_fact.typed_parameters.clone(),
        facts: dom,
        line_file: line,
    }))
}

// (and A_i) or (and B_j) = and_{i,j}(A_i or B_j).
fn disjoin_conjunctions(
    runtime: &mut Runtime,
    left: &[QuantifierFreeFact],
    right: &[QuantifierFreeFact],
    line: Option<SourceLine>,
) -> Result<Vec<QuantifierFreeFact>, String> {
    let mut clauses = Vec::new();
    for a in left {
        for b in right {
            let clause = runtime
                .disjoin_quantifier_free_facts(&[a.clone(), b.clone()], line.clone())
                .map_err(|e| format!("by contra: cannot build iff counterexample: {e:?}"))?
                .ok_or_else(|| "by contra: empty iff counterexample clause".to_string())?;
            clauses.push(clause);
        }
    }
    Ok(clauses)
}
