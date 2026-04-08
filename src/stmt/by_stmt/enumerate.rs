use crate::prelude::*;
use std::fmt;

/// Prove by finite enumeration (`by enumerate …`).
#[derive(Clone)]
pub struct ByEnumerateStmt {
    pub params: Vec<String>,
    pub param_sets: Vec<ListSet>,
    pub to_prove: Vec<ExistOrAndChainAtomicFact>,
    pub proof: Vec<Stmt>,
    pub line_file: LineFile,
}

impl ByEnumerateStmt {
    pub fn new(
        params: Vec<String>,
        param_sets: Vec<ListSet>,
        to_prove: Vec<ExistOrAndChainAtomicFact>,
        proof: Vec<Stmt>,
        line_file: LineFile,
    ) -> Self {
        ByEnumerateStmt {
            params,
            param_sets,
            to_prove,
            proof,
            line_file,
        }
    }

    /// Same parameters as `list { ... }` in the header; `dom_facts` empty; `then_facts` are `to_prove`.
    pub fn to_corresponding_forall_fact(&self) -> Result<Fact, String> {
        if self.params.len() != self.param_sets.len() {
            return Err(
                "by enumerate: number of params does not match number of list sets".to_string(),
            );
        }
        let mut params_def_with_type: Vec<ParamGroupWithParamType> = Vec::new();
        for (param_name, list_set_obj) in self.params.iter().zip(self.param_sets.iter()) {
            params_def_with_type.push(ParamGroupWithParamType::new(
                vec![param_name.clone()],
                ParamType::Obj(Obj::ListSet(list_set_obj.clone())),
            ));
        }
        let forall_fact = ForallFact::new(
            params_def_with_type,
            vec![],
            self.to_prove.clone(),
            self.line_file.clone(),
        );
        Ok(Fact::ForallFact(forall_fact))
    }
}

impl fmt::Display for ByEnumerateStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} {} {}{}\n{}{}\n{}\n{}",
            BY,
            ENUMERATE,
            vec_pair_to_string(&self.params, &self.param_sets),
            COLON,
            add_four_spaces_at_beginning(PROVE.to_string(), 1),
            COLON,
            vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.proof, 2),
            vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.to_prove, 1),
        )
    }
}
