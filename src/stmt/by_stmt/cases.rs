use crate::prelude::*;
use std::fmt;

/// Prove a fact by exhaustive case split (`by cases:`).
#[derive(Clone)]
pub struct ByCasesStmt {
    pub cases: Vec<AndChainAtomicFact>,
    pub then_facts: Vec<Fact>,
    pub proofs: Vec<Vec<Stmt>>,
    pub impossible_facts: Vec<Option<AtomicFact>>,
    pub line_file: LineFile,
}

impl ByCasesStmt {
    pub fn new(
        cases: Vec<AndChainAtomicFact>,
        then_facts: Vec<Fact>,
        proofs: Vec<Vec<Stmt>>,
        impossible_facts: Vec<Option<AtomicFact>>,
        line_file: LineFile,
    ) -> Self {
        ByCasesStmt {
            cases,
            then_facts,
            proofs,
            impossible_facts,
            line_file,
        }
    }
}

impl fmt::Display for ByCasesStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let case_and_proof_of_each_case = self
            .cases
            .iter()
            .zip(self.proofs.iter())
            .zip(self.impossible_facts.iter())
            .map(|((case, proof), impossible_fact)| {
                if let Some(impossible_fact) = impossible_fact {
                    format!(
                        "{} {}{}\n{}\n{} {}",
                        add_four_spaces_at_beginning(CASE.to_string(), 1),
                        case,
                        COLON,
                        vec_to_string_add_four_spaces_at_beginning_of_each_line(proof, 2),
                        add_four_spaces_at_beginning(IMPOSSIBLE.to_string(), 2),
                        &impossible_fact.to_string()
                    )
                } else {
                    format!(
                        "{} {}{}\n{}",
                        add_four_spaces_at_beginning(CASE.to_string(), 1),
                        case,
                        COLON,
                        vec_to_string_add_four_spaces_at_beginning_of_each_line(proof, 2)
                    )
                }
            })
            .collect::<Vec<String>>();

        write!(
            f,
            "{} {}{}\n{}{}\n{}\n{}",
            BY,
            CASES,
            COLON,
            add_four_spaces_at_beginning(PROVE.to_string(), 1),
            COLON,
            vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.then_facts, 1),
            case_and_proof_of_each_case.join("\n")
        )
    }
}
