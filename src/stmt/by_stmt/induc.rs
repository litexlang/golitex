use crate::prelude::*;
use std::fmt;

/// Prove by induction on an integer (`by induc ... from ...`) or strong induction (`by strong_induc ... from ...`).
#[derive(Clone)]
pub struct ByInducStmt {
    pub to_prove: Vec<ExistOrAndChainAtomicFact>,
    pub proof: Vec<Stmt>,
    pub base_proof: Option<Vec<Stmt>>,
    pub step_proof: Option<Vec<Stmt>>,
    pub param: String,
    pub induc_from: Obj,
    /// When true, the induction step uses `forall y` with `m <= y <= n` as the hypothesis band (strong / complete induction).
    pub strong: bool,
    pub line_file: LineFile,
}

impl ByInducStmt {
    pub fn new(
        fact: Vec<ExistOrAndChainAtomicFact>,
        param: String,
        induc_from: Obj,
        proof: Vec<Stmt>,
        base_proof: Option<Vec<Stmt>>,
        step_proof: Option<Vec<Stmt>>,
        line_file: LineFile,
        strong: bool,
    ) -> Self {
        ByInducStmt {
            to_prove: fact,
            proof,
            base_proof,
            step_proof,
            param,
            induc_from,
            strong,
            line_file,
        }
    }

    pub fn has_structured_proof(&self) -> bool {
        self.base_proof.is_some() || self.step_proof.is_some()
    }
}

impl fmt::Display for ByInducStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let question_goals = self
            .to_prove
            .iter()
            .map(|fact| format!("{} {}", QUESTION_GOAL, fact))
            .collect::<Vec<String>>();
        if self.has_structured_proof() {
            let keyword = if self.strong { STRONG_INDUC } else { INDUC };
            let step_keyword = if self.strong { STRONG_INDUC } else { INDUC };
            let base_proof = match &self.base_proof {
                Some(proof) => vec_to_string_add_four_spaces_at_beginning_of_each_line(proof, 2),
                None => String::new(),
            };
            let step_proof = match &self.step_proof {
                Some(proof) => vec_to_string_add_four_spaces_at_beginning_of_each_line(proof, 2),
                None => String::new(),
            };
            return write!(
                f,
                "{} {} {} {} {}{}\n{}\n{} {} {} {} {}{}\n{}\n{} {}{}\n{}",
                BY,
                keyword,
                self.param,
                FROM,
                self.induc_from,
                COLON,
                vec_to_string_add_four_spaces_at_beginning_of_each_line(&question_goals, 1),
                add_four_spaces_at_beginning(QUESTION_GOAL.to_string(), 1),
                FROM,
                self.param,
                EQUAL,
                self.induc_from,
                COLON,
                base_proof,
                add_four_spaces_at_beginning(QUESTION_GOAL.to_string(), 1),
                step_keyword,
                COLON,
                step_proof,
            );
        }

        if self.strong {
            write!(
                f,
                "{} {} {} {} {}{}\n{}\n{}",
                BY,
                STRONG_INDUC,
                self.param,
                FROM,
                self.induc_from,
                COLON,
                vec_to_string_add_four_spaces_at_beginning_of_each_line(&question_goals, 1),
                vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.proof, 1),
            )
        } else {
            write!(
                f,
                "{} {} {} {} {}{}\n{}\n{}",
                BY,
                INDUC,
                self.param,
                FROM,
                self.induc_from,
                COLON,
                vec_to_string_add_four_spaces_at_beginning_of_each_line(&question_goals, 1),
                vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.proof, 1),
            )
        }
    }
}
