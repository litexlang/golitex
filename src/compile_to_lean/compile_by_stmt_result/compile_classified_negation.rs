use super::compile_by_contra_stmt_result::validate_atomic_negation;
use crate::compile_to_lean::compile_compound_fact::chain_edge;
use crate::compile_to_lean::LeanCompileError;
use crate::prelude::*;

// The executor classifies QF negation by ordered DNF distribution. Check that
// exact classification before using a fixed propositional normalization bridge.
pub(super) fn validate_classified_negation(
    source: &Fact,
    negative: &Fact,
) -> Result<(), LeanCompileError> {
    if let (Fact::ExistUniqueFact(source), Fact::ForallFact(negative)) = (source, negative) {
        return super::compile_unique_contra::validate_unique_negation(source, negative);
    }
    if let (Fact::ForallFact(positive), Fact::NotForall(negative))
    | (Fact::NotForall(negative), Fact::ForallFact(positive)) = (source, negative)
    {
        if positive.fact_id != negative.fact_id
            && positive.typed_parameters == negative.typed_parameters
            && positive.dom_facts
                == negative
                    .dom_facts
                    .iter()
                    .cloned()
                    .map(crate::instantiate::quantifier_free_fact_to_fact)
                    .collect::<Vec<_>>()
            && positive
                .then_facts
                .iter()
                .cloned()
                .map(Fact::from)
                .collect::<Vec<_>>()
                == negative
                    .then_facts
                    .iter()
                    .cloned()
                    .map(crate::instantiate::quantifier_free_fact_to_fact)
                    .collect::<Vec<_>>()
        {
            return Ok(());
        }
        return Err(LeanCompileError::unsupported("By/ForallNegationSubject"));
    }
    if let (Fact::ExistFact(left), Fact::NotExistFact(right))
    | (Fact::NotExistFact(left), Fact::ExistFact(right)) = (source, negative)
    {
        if crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_they_are_the_same::helper::plain_exist_facts_alpha_equal(left, right) {
            return Ok(());
        }
        return Err(LeanCompileError::unsupported("By/ExistNegationSubject"));
    }
    if matches!(
        (source, negative),
        (Fact::AtomicFact(_), Fact::AtomicFact(_))
    ) {
        return validate_atomic_negation(source, negative).map(|_| ());
    }
    let clauses = quantifier_free_terms(source)?;
    let actual = quantifier_free_terms(negative)?;
    let mut expected: Vec<Vec<AtomicFact>> = vec![Vec::new()];
    for clause in clauses {
        let mut next = Vec::new();
        for prefix in &expected {
            for atom in &clause {
                let negated = crate::ast::fact::negate_atomic_fact(atom, negative.fact_id())
                    .ok_or_else(|| LeanCompileError::unsupported("By/AtomicNegationFamily"))?;
                let mut term = prefix.clone();
                term.push(negated);
                next.push(term);
            }
        }
        expected = next;
    }
    if expected.len() != actual.len()
        || expected.iter().zip(&actual).any(|(expected, actual)| {
            expected.len() != actual.len()
                || expected.iter().zip(actual).any(|(a, b)| a.ir() != b.ir())
        })
    {
        return Err(LeanCompileError::new(
            "By/NegationSubject",
            "The ordered classified negation differs from the original complete formula.",
        ));
    }
    Ok(())
}

pub(super) fn classified_negation_bridge(proof: &str) -> String {
    format!("(by\n  classical\n  simpa only [not_and_or, not_or, not_not, and_or_left, or_and_right, and_assoc, or_assoc] using {proof})")
}

pub(in crate::compile_to_lean) fn quantifier_free_terms(
    fact: &Fact,
) -> Result<Vec<Vec<AtomicFact>>, LeanCompileError> {
    let terms = match fact {
        Fact::AtomicFact(atom) => vec![vec![atom.clone()]],
        Fact::AndFact(and) => vec![and.facts.clone()],
        Fact::ChainFact(chain) => vec![(0..chain.prop_names.len())
            .map(|index| chain_edge(chain, index, chain.fact_id))
            .collect::<Result<Vec<_>, _>>()?],
        Fact::OrFact(or) => {
            let mut terms = Vec::new();
            for branch in &or.facts {
                terms.extend(quantifier_free_terms(
                    &crate::ast::fact::and_chain_as_fact(branch),
                )?);
            }
            terms
        }
        _ => return Err(LeanCompileError::unsupported("By/ClassifiedNegation")),
    };
    if terms.is_empty() || terms.iter().any(Vec::is_empty) {
        return Err(LeanCompileError::unsupported("By/EmptyNegation"));
    }
    Ok(terms)
}

/// Validate the producer's smaller CNF/DNF counterexample body. This compares
/// syntax and allocates no source identities or verification evidence.
pub(in crate::compile_to_lean) fn validate_negated_conjunction(
    source: &[QuantifierFreeFact],
    negative: &[QuantifierFreeFact],
) -> Result<(), LeanCompileError> {
    if source.is_empty() || negative.is_empty() {
        return Err(LeanCompileError::unsupported("NotForall/EmptyBody"));
    }
    let mut parts = Vec::new();
    let (mut cnf_count, mut cnf_atoms, mut dnf_atoms) = (1usize, 0usize, 0usize);
    for fact in source {
        let clauses = quantifier_free_terms(&crate::instantiate::quantifier_free_fact_to_fact(
            fact.clone(),
        ))?;
        let clauses = clauses
            .into_iter()
            .map(|clause| {
                clause
                    .into_iter()
                    .map(|atom| {
                        crate::ast::fact::negate_atomic_fact(&atom, atom.fact_id()).ok_or_else(
                            || LeanCompileError::unsupported("NotForall/NegationFamily"),
                        )
                    })
                    .collect::<Result<Vec<_>, _>>()
            })
            .collect::<Result<Vec<_>, _>>()?;
        let count = clauses.len();
        let atoms = clauses
            .iter()
            .fold(0usize, |n, c| n.saturating_add(c.len()));
        cnf_atoms = cnf_atoms
            .saturating_mul(count)
            .saturating_add(atoms.saturating_mul(cnf_count));
        cnf_count = cnf_count.saturating_mul(count);
        let terms = clauses
            .iter()
            .fold(1usize, |n, c| n.saturating_mul(c.len()));
        dnf_atoms = dnf_atoms.saturating_add(terms.saturating_mul(count));
        parts.push(clauses);
    }
    let expected = if dnf_atoms < cnf_atoms {
        let mut alternatives = Vec::new();
        for clauses in parts {
            let mut terms = vec![Vec::new()];
            for clause in clauses {
                terms = terms
                    .iter()
                    .flat_map(|prefix| {
                        clause.iter().map(move |atom| {
                            let mut term = prefix.clone();
                            term.push(atom.clone());
                            term
                        })
                    })
                    .collect();
            }
            alternatives.extend(terms);
        }
        vec![alternatives]
    } else {
        let mut combined = parts.remove(0);
        for part in parts {
            combined = combined
                .iter()
                .flat_map(|left| {
                    part.iter()
                        .map(move |right| left.iter().chain(right).cloned().collect::<Vec<_>>())
                })
                .collect();
        }
        combined
            .into_iter()
            .map(|clause| clause.into_iter().map(|atom| vec![atom]).collect())
            .collect()
    };
    let actual = negative
        .iter()
        .map(|fact| {
            quantifier_free_terms(&crate::instantiate::quantifier_free_fact_to_fact(
                fact.clone(),
            ))
        })
        .collect::<Result<Vec<_>, _>>()?;
    let signatures = |parts: Vec<Vec<Vec<AtomicFact>>>| {
        parts
            .into_iter()
            .map(|terms| {
                terms
                    .into_iter()
                    .map(|clause| clause.into_iter().map(|atom| atom.ir()).collect::<Vec<_>>())
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>()
    };
    if signatures(expected) != signatures(actual) {
        return Err(LeanCompileError::new(
            "NotForall/NegatedBody",
            "The counterexample differs from the original ordered CNF/DNF negation.",
        ));
    }
    Ok(())
}
