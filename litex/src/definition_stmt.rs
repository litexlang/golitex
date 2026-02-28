use crate::parameter_type::ParameterType;
use crate::fact::{ Fact};
use crate::obj::Obj;
use std::fmt;
use crate::consts::{COLON, CONSTRUCT, DOM, EQUAL, FN, HAVE, LET, PROP, RIGHT_ARROW};
use crate::helper::{add_four_spaces_at_beginning, braced_pair_vec_to_string, braced_vec_to_string, vec_pair_to_string, vec_to_string_add_four_spaces_at_beginning_of_each_line, vec_to_string_join_by_comma};
use crate::obj::FnSetWithParams;
use crate::stmt::Stmt;

pub enum DefStmt {
    DefLetStmt(DefLetStmt),
    DefPropStmt(DefPropStmt),
    HaveObjInNonemptySetStmt(HaveObjInNonemptySetStmt),
    HaveObjEqualStmt(HaveObjEqualStmt),
    LetFnStmt(LetFnStmt),
    HaveFnStmt(HaveFnStmt),
}

pub struct HaveFnStmt {
    pub fn_set_with_params: FnSetWithParams,
    pub proof: Vec<Stmt>,
    pub construct_fn_equal_to: Obj,
    pub line: u32,
    pub file_index: usize,
}

pub struct LetFnStmt {
    pub fn_set_with_params: FnSetWithParams,
    pub line: u32,
    pub file_index: usize,
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
            DefStmt::HaveFnStmt(have_fn_stmt) => write!(f, "{}", have_fn_stmt),
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
            DefStmt::HaveFnStmt(have_fn_stmt) => (have_fn_stmt.line, have_fn_stmt.file_index),
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

impl LetFnStmt {
    pub fn new(fn_set_with_params: FnSetWithParams, line: u32, file_index: usize) -> Self {
        LetFnStmt { fn_set_with_params, line, file_index }
    }
}

fn multiple_line_fn_stmt_str(fn_set_with_params: &FnSetWithParams) -> String {
    let name = &fn_set_with_params.fn_name;
    let params = &fn_set_with_params.params;
    let param_sets = &fn_set_with_params.param_sets;
    let dom_facts = &fn_set_with_params.dom_facts;
    let then_facts = &fn_set_with_params.then_facts;
    let ret_set = &fn_set_with_params.ret_set;
    
    let dom_empty = dom_facts.is_empty();
    let then_empty = then_facts.is_empty();
    let header = format!("{} {}{}\n{}{}{}", FN, name, COLON, add_four_spaces_at_beginning(FN, 1), braced_pair_vec_to_string(params, param_sets), COLON);
    let ret = ret_set.to_string();
    match (dom_empty, then_empty) {
        (true, true) => format!("{}\n{}{}\n{}", header, add_four_spaces_at_beginning(RIGHT_ARROW, 2), COLON, ret),
        (true, false) => format!("{}\n{}{}\n{}\n{}", header, add_four_spaces_at_beginning(RIGHT_ARROW, 2), COLON, ret, vec_to_string_add_four_spaces_at_beginning_of_each_line(then_facts, 3)),
        (false, true) => format!("{}\n{}{}\n{}\n{}{}\n{}", header, add_four_spaces_at_beginning(DOM, 2), COLON, vec_to_string_add_four_spaces_at_beginning_of_each_line(dom_facts, 3), add_four_spaces_at_beginning(RIGHT_ARROW, 2), COLON, ret),
        (false, false) => format!("{}\n{}{}\n{}\n{}{}\n{}\n{}", header, add_four_spaces_at_beginning(DOM, 2), COLON, vec_to_string_add_four_spaces_at_beginning_of_each_line(dom_facts, 3), add_four_spaces_at_beginning(RIGHT_ARROW, 2), COLON, ret, vec_to_string_add_four_spaces_at_beginning_of_each_line(then_facts, 3)),
    }
}

impl fmt::Display for LetFnStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", multiple_line_fn_stmt_str(&self.fn_set_with_params))
    }
}

impl fmt::Display for HaveFnStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let construct_str_and_proof = match self.proof.len() { 0 => format!("{} {}{} {}{}", add_four_spaces_at_beginning(CONSTRUCT, 1), self.fn_set_with_params.fn_name, braced_vec_to_string(&self.fn_set_with_params.params), EQUAL, self.construct_fn_equal_to), _ => format!("{} {}{} {}{}{}\n{}", add_four_spaces_at_beginning(CONSTRUCT, 1), self.fn_set_with_params.fn_name, braced_vec_to_string(&self.fn_set_with_params.params), EQUAL, self.construct_fn_equal_to, COLON, vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.proof, 2)) };
        
        write!(f, "{}\n{}", multiple_line_fn_stmt_str(&self.fn_set_with_params), construct_str_and_proof)
    }
}

impl HaveFnStmt {
    pub fn new(fn_set_with_params: FnSetWithParams, proof: Vec<Stmt>, construct_fn_equal_to: Obj, line: u32, file_index: usize) -> Self {
        HaveFnStmt { fn_set_with_params, proof, construct_fn_equal_to, line, file_index }
    }
}