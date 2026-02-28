use crate::parameter_type::ParameterType;
use crate::fact::Fact;
use crate::atomic_fact::AtomicFact;
use crate::obj::Obj;
use std::fmt;
use crate::consts::{LET, COLON, PROP, HAVE, EQUAL, LEFT_BRACE, RIGHT_BRACE, FN};
use crate::helper::{vec_pair_to_string, vec_to_string_add_four_spaces_at_beginning_of_each_line, vec_to_string_join_by_comma};

pub enum DefStmt {
    DefLetStmt(DefLetStmt),
    DefPropStmt(DefPropStmt),
    HaveObjInNonemptySetStmt(HaveObjInNonemptySetStmt),
    HaveObjEqualStmt(HaveObjEqualStmt),
    LetFnStmt(LetFnStmt),
}

pub struct LetFnStmt {
    pub def_header_with_dom: DefHeaderWithParamSetAndDomFacts,
    pub ret_set: Obj,
    pub facts: Vec<Fact>,
    pub line: u32,
    pub file_index: usize,
}

pub struct DefHeaderWithParamSetAndDomFacts {
    pub name: String,
    pub params: Vec<String>,
    pub param_sets: Vec<Obj>,
    pub dom_facts: Vec<AtomicFact>,
}

pub struct HaveObjEqualStmt {
    pub names: Vec<String>,
    pub param_types: Vec<ParameterType>,
    pub objs_equal_to: Vec<Obj>,
    pub line: u32,
    pub file_index: usize,
}

pub struct HaveObjInNonemptySetStmt {
    pub names: Vec<String>,
    pub param_types: Vec<ParameterType>,
    pub line: u32,
    pub file_index: usize,
}

pub struct DefHeaderWithParamType {
    pub name: String,
    pub param_names: Vec<String>,
    pub param_types: Vec<ParameterType>,
}

pub struct DefLetStmt {
    pub names: Vec<String>,
    pub param_types: Vec<ParameterType>,
    pub facts: Vec<Fact>,
    pub line: u32,
    pub file_index: usize,
}

pub struct DefPropStmt {
    pub def_header: DefHeaderWithParamType,
    pub iff_facts: Option<Vec<Fact>>,
    pub line: u32,
    pub file_index: usize,
}

impl fmt::Display for DefStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DefStmt::DefLetStmt(def_let_stmt) => write!(f, "{}", def_let_stmt),
            DefStmt::DefPropStmt(def_prop_stmt) => write!(f, "{}", def_prop_stmt),
            DefStmt::HaveObjInNonemptySetStmt(have_obj_in_nonempty_set_stmt) => write!(f, "{}", have_obj_in_nonempty_set_stmt),
            DefStmt::HaveObjEqualStmt(have_obj_equal_stmt) => write!(f, "{}", have_obj_equal_stmt),
            DefStmt::LetFnStmt(let_fn_stmt) => write!(f, "{}", let_fn_stmt),
        }
    }
}

impl DefPropStmt {
    pub fn new(def_header: DefHeaderWithParamType, iff_facts: Option<Vec<Fact>>, line: u32, file_index: usize) -> Self {
        DefPropStmt { def_header, iff_facts, line, file_index }
    }
}

impl fmt::Display for DefPropStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.iff_facts {
            Some(iff_facts) => write!(f, "{} {}{}\n{}", PROP, self.def_header, COLON, vec_to_string_add_four_spaces_at_beginning_of_each_line(&iff_facts, 1)),
            None => write!(f, "{} {}", PROP, self.def_header),
        }
    }
}

impl DefHeaderWithParamType {
    pub fn new(name: String, param_names: Vec<String>, param_types: Vec<ParameterType>) -> Self {
        DefHeaderWithParamType { name, param_names, param_types }
    }
}

impl fmt::Display for DefHeaderWithParamType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}", self.name, vec_pair_to_string(&self.param_names, &self.param_types))
    }
}

impl DefLetStmt {
    pub fn new(names: Vec<String>, param_types: Vec<ParameterType>, facts: Vec<Fact>, line: u32, file_index: usize) -> Self {
        DefLetStmt { names, param_types, facts, line, file_index }
    }
}

impl fmt::Display for DefLetStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.facts.len() {
            0 => write!(f, "{} {}", LET, vec_pair_to_string(&self.names, &self.param_types)),
            _ => write!(f, "{} {}{}\n{}", LET, vec_pair_to_string(&self.names, &self.param_types), COLON, vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.facts, 1)),
        }
    }
}

impl DefStmt {
    pub fn line_file(&self) -> (u32, usize) {
        match self {
            DefStmt::DefLetStmt(def_let_stmt) => (def_let_stmt.line, def_let_stmt.file_index),
            DefStmt::DefPropStmt(def_prop_stmt) => (def_prop_stmt.line, def_prop_stmt.file_index),
            DefStmt::HaveObjInNonemptySetStmt(have_obj_in_nonempty_set_stmt) => (have_obj_in_nonempty_set_stmt.line, have_obj_in_nonempty_set_stmt.file_index),
            DefStmt::HaveObjEqualStmt(have_obj_equal_stmt) => (have_obj_equal_stmt.line, have_obj_equal_stmt.file_index),
            DefStmt::LetFnStmt(let_fn_stmt) => (let_fn_stmt.line, let_fn_stmt.file_index),
        }
    }
}

impl HaveObjInNonemptySetStmt {
    pub fn new(names: Vec<String>, param_types: Vec<ParameterType>, line: u32, file_index: usize) -> Self {
        HaveObjInNonemptySetStmt { names, param_types, line, file_index }
    }
}

impl fmt::Display for HaveObjInNonemptySetStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}", HAVE, vec_pair_to_string(&self.names, &self.param_types))
    }
}

impl HaveObjEqualStmt {
    pub fn new(names: Vec<String>, param_types: Vec<ParameterType>, objs_equal_to: Vec<Obj>, line: u32, file_index: usize) -> Self {
        HaveObjEqualStmt { names, param_types, objs_equal_to, line, file_index }
    }
}

impl fmt::Display for HaveObjEqualStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {} {} {}", HAVE, vec_pair_to_string(&self.names, &self.param_types), EQUAL, vec_to_string_join_by_comma(&self.objs_equal_to))
    }
}

impl DefHeaderWithParamSetAndDomFacts {
    pub fn new(name: String, params: Vec<String>, param_sets: Vec<Obj>, dom_facts: Vec<AtomicFact>) -> Self {
        DefHeaderWithParamSetAndDomFacts { name, params, param_sets, dom_facts }
    }
}

impl fmt::Display for DefHeaderWithParamSetAndDomFacts {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.dom_facts.len() {
            0 => write!(f, "{} {}{}{}", self.name, LEFT_BRACE, vec_pair_to_string(&self.params, &self.param_sets), RIGHT_BRACE),
            _ => write!(f, "{} {}{} {} {}{}", self.name, LEFT_BRACE, vec_pair_to_string(&self.params, &self.param_sets), COLON, vec_to_string_join_by_comma(&self.dom_facts), RIGHT_BRACE),
    }
}
}

impl LetFnStmt {
    pub fn new(def_header_with_dom: DefHeaderWithParamSetAndDomFacts, ret_set: Obj, facts: Vec<Fact>, line: u32, file_index: usize) -> Self {
        LetFnStmt { def_header_with_dom, ret_set, facts, line, file_index }
    }
}

impl fmt::Display for LetFnStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {} {}{}{}\n{}", LET, FN, self.def_header_with_dom, COLON, self.ret_set,vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.facts, 1))
    }
}