use crate::parameter_type::ParameterType;
use crate::fact::Fact;
use std::fmt;
use crate::consts::{LET, COLON, PROP};
use crate::helper::{vec_pair_to_string, add_four_spaces_to_vec_at_beginning, str_with_line_file};

pub struct DefHeader {
    name: String,
    param_names: Vec<String>,
    param_types: Vec<ParameterType>,
}

pub struct DefLetStmt {
    names: Vec<String>,
    param_types: Vec<ParameterType>,
    facts: Vec<Fact>,
    line: u32,
    file_index: usize,
}

pub struct DefPropStmt {
    def_header: DefHeader,
    iff_facts: Option<Vec<Fact>>,
    line: u32,
    file_index: usize,
}

impl DefPropStmt {
    pub fn new(def_header: DefHeader, iff_facts: Option<Vec<Fact>>, line: u32, file_index: usize) -> Self {
        DefPropStmt { def_header, iff_facts, line, file_index }
    }

    pub fn str_with_line_file(&self) -> String {
        return str_with_line_file(&self.to_string(), self.line, self.file_index);
    }
}

impl fmt::Display for DefPropStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.iff_facts {
            Some(iff_facts) => write!(f, "{} {}{}\n{}", PROP, self.def_header, COLON, add_four_spaces_to_vec_at_beginning(&iff_facts, 1)),
            None => write!(f, "{} {}", PROP, self.def_header),
        }
    }
}

impl DefHeader {
    pub fn new(name: String, param_names: Vec<String>, param_types: Vec<ParameterType>) -> Self {
        DefHeader { name, param_names, param_types }
    }
}

impl fmt::Display for DefHeader {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}", self.name, vec_pair_to_string(&self.param_names, &self.param_types))
    }
}

impl DefLetStmt {
    pub fn new(names: Vec<String>, param_types: Vec<ParameterType>, facts: Vec<Fact>, line: u32, file_index: usize) -> Self {
        DefLetStmt { names, param_types, facts, line, file_index }
    }

    pub fn str_with_line_file(&self) -> String {
        return str_with_line_file(&self.to_string(), self.line, self.file_index);
    }
}

impl fmt::Display for DefLetStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.facts.len() {
            0 => write!(f, "{} {}", LET, vec_pair_to_string(&self.names, &self.param_types)),
            _ => write!(f, "{} {}{}\n{}", LET, vec_pair_to_string(&self.names, &self.param_types), COLON, add_four_spaces_to_vec_at_beginning(&self.facts, 1)),
        }
    }
}