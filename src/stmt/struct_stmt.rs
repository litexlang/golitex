use crate::prelude::*;
use std::fmt;

#[derive(Clone)]
pub struct DefStructStmt {
    pub name: String,
    pub param_def_with_dom: Option<(ParamDefWithType, Vec<OrAndChainAtomicFact>)>,
    pub fields: Vec<(String, Obj)>,
    pub equivalent_facts: Vec<Fact>,
    pub line_file: LineFile,
}

impl DefStructStmt {
    pub fn new(
        name: String,
        param_def_with_dom: Option<(ParamDefWithType, Vec<OrAndChainAtomicFact>)>,
        fields: Vec<(String, Obj)>,
        equivalent_facts: Vec<Fact>,
        line_file: LineFile,
    ) -> Self {
        DefStructStmt {
            name,
            param_def_with_dom,
            fields,
            equivalent_facts,
            line_file,
        }
    }

    pub fn stmt_type_name(&self) -> String {
        "DefStructStmt".to_string()
    }
}

impl fmt::Display for DefStructStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let params = match &self.param_def_with_dom {
            Some((param_def, _)) => format!("{}", param_def),
            None => String::new(),
        };
        if params.is_empty() {
            write!(f, "{} {}{}", STRUCT, self.name, COLON)
        } else {
            write!(
                f,
                "{} {}{}{}{}{}",
                STRUCT, self.name, LESS, params, GREATER, COLON
            )
        }
    }
}
