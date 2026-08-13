use crate::prelude::*;
use std::fmt;

#[derive(Clone)]
pub struct StructFieldDef {
    pub binding: SymbolBinding,
    pub field_type: Obj,
}

#[derive(Clone)]
pub struct DefStructStmt {
    pub name: String,
    pub param_def_with_dom: Option<(ParamDefWithType, Vec<QuantifierFreeFact>)>,
    pub fields: Vec<StructFieldDef>,
    pub equivalent_facts: Vec<Fact>,
    pub line_file: LineFile,
}

impl DefStructStmt {
    pub fn new(
        name: String,
        param_def_with_dom: Option<(ParamDefWithType, Vec<QuantifierFreeFact>)>,
        fields: Vec<StructFieldDef>,
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

    pub fn output_type_string() -> String {
        "structure definition".to_string()
    }
}

impl StructFieldDef {
    pub fn new(binding: SymbolBinding, field_type: Obj) -> Self {
        StructFieldDef {
            binding,
            field_type,
        }
    }

    pub fn name(&self) -> &str {
        self.binding.name()
    }
}

impl fmt::Display for DefStructStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
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
