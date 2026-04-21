use crate::prelude::*;
use std::fmt;

/// Prove by induction on an integer (`by induc … from …`).
#[derive(Clone)]
pub struct ByInducStmt {
    pub to_prove: Vec<ExistOrAndChainAtomicFact>,
    pub proof: Vec<Stmt>,
    pub param: String,
    pub induc_from: Obj,
    pub line_file: LineFile,
}

impl ByInducStmt {
    pub fn new(
        fact: Vec<ExistOrAndChainAtomicFact>,
        param: String,
        induc_from: Obj,
        proof: Vec<Stmt>,
        line_file: LineFile,
    ) -> Self {
        ByInducStmt {
            to_prove: fact,
            proof,
            param,
            induc_from,
            line_file,
        }
    }
}

impl fmt::Display for ByInducStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} {} {} {} {}{}\n{}{}\n{}\n{}",
            BY,
            INDUC,
            self.param,
            FROM,
            self.induc_from,
            COLON,
            add_four_spaces_at_beginning(PROVE.to_string(), 1),
            COLON,
            vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.to_prove, 2),
            vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.proof, 1),
        )
    }
}
