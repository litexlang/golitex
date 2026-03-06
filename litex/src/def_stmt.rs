use crate::parameter_type::ParameterType;
use crate::fact::Fact;
use std::fmt;
use crate::keywords{LET, COLON, PROP};
use crate::helper::{vec_pair_to_string, add_four_spaces_to_vec_at_beginning};

pub enum DefStmt<'a> {
    DefLetStmt(DefLetStmt<'a>),
    DefPropStmt(DefPropStmt<'a>),
}

pub struct DefHeader {
    name: String,
    param_names: Vec<String>,
    param_types: Vec<ParameterType>,
}

pub struct DefLetStmt<'a> {
    names: Vec<String>,
    param_types: Vec<ParameterType>,
    facts: Vec<Fact<'a>>,
    line: u32,
    file: &'a str,
}

pub struct DefPropStmt<'a> {
    def_header: DefHeader,
    iff_facts: Option<Vec<Fact<'a>>>,
    line: u32,
    file: &'a str,
}

impl fmt::Display for DefStmt<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DefStmt::DefLetStmt(def_let_stmt) => write!(f, "{}", def_let_stmt),
            DefStmt::DefPropStmt(def_prop_stmt) => write!(f, "{}", def_prop_stmt),
        }
    }
}

impl<'a> DefPropStmt<'a> {
    pub fn new(def_header: DefHeader, iff_facts: Option<Vec<Fact<'a>>>, line: u32, file: &'a str) -> Self {
        DefPropStmt { def_header, iff_facts, line, file }
    }
}

impl fmt::Display for DefPropStmt<'_> {
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

impl<'a> DefLetStmt<'a> {
    pub fn new(names: Vec<String>, param_types: Vec<ParameterType>, facts: Vec<Fact<'a>>, line: u32, file: &'a str) -> Self {
        DefLetStmt { names, param_types, facts, line, file }
    }
}

impl fmt::Display for DefLetStmt<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.facts.len() {
            0 => write!(f, "{} {}", LET, vec_pair_to_string(&self.names, &self.param_types)),
            _ => write!(f, "{} {}{}\n{}", LET, vec_pair_to_string(&self.names, &self.param_types), COLON, add_four_spaces_to_vec_at_beginning(&self.facts, 1)),
        }
    }
}

impl DefStmt<'_> {
    pub fn line_file(&self) -> (u32, &str) {
        match self {
            DefStmt::DefLetStmt(def_let_stmt) => (def_let_stmt.line, def_let_stmt.file),
            DefStmt::DefPropStmt(def_prop_stmt) => (def_prop_stmt.line, def_prop_stmt.file),
        }
    }
}