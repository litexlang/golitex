use crate::or_fact_or_and_fact_or_specific_fact::OrFactOrAndFactOrSpecFact;
use crate::parameter_type_and_property::{ParameterType, ParamDefWithParamTypeAndProperty};
use crate::fact::{ Fact};
use crate::obj::{Obj};
use std::fmt;
use crate::keywords::{CASE, COLON, COMMA, DOM, EQUAL, FN, HAVE, LEFT_BRACE, LET, PROP, RIGHT_ARROW, RIGHT_BRACE, SET_TEMPLATE};
use crate::helper::{add_four_spaces_at_beginning,   braced_vec_to_string, to_string_and_add_four_spaces_at_beginning_of_each_line, vec_pair_to_string, vec_to_string_add_four_spaces_at_beginning_of_each_line, vec_to_string_join_by_comma, vec_to_string_with_sep};
use crate::obj::FnSetWithDom;
use crate::and_fact_or_specific_fact::AndFactOrSpecFact;
use crate::exist_fact::TrueExistFact;
use crate::define_algorithm_stmt::DefineAlgorithmStmt;

pub enum DefStmt {
    DefLetStmt(DefLetStmt),
    DefPropStmt(DefPropStmt),
    HaveObjInNonemptySetStmt(HaveObjInNonemptySetOrParamTypeStmt),
    HaveObjEqualStmt(HaveObjEqualStmt),
    LetFnStmt(LetFnStmt),
    HaveObjStStmt(HaveObjStStmt),
    HaveFnEqualStmt(HaveFnEqualStmt),
    HaveFnEqualCaseByCaseStmt(HaveFnEqualCaseByCaseStmt),
    DefSetTemplateStmt(DefSetTemplateStmt),
    DefineAlgorithmStmt(DefineAlgorithmStmt),
}

pub struct DefSetTemplateStmt {
    pub name: String,
    pub params_def_with_type: Vec<ParamDefWithParamTypeAndProperty>,
    pub dom_facts: Vec<OrFactOrAndFactOrSpecFact>,
    pub equal_to: Obj,
    pub line_file_index: Option<(usize, usize)>,
}

pub struct HaveFnEqualCaseByCaseStmt {
    pub name: String,
    pub fn_set_with_params: FnSetWithDom,
    pub cases: Vec<AndFactOrSpecFact>,
    pub equal_tos: Vec<Obj>,
    pub line_file_index: Option<(usize, usize)>,
}

pub struct HaveFnEqualStmt {
    pub name: String,
    pub fn_set_with_params: FnSetWithDom,
    pub equal_to: Obj,
    pub line_file_index: Option<(usize, usize)>,
}

pub struct HaveObjStStmt {
    pub exist_fact_in_have_obj_st: TrueExistFact,
    pub line_file_index: Option<(usize, usize)>,
}

pub struct LetFnStmt {
    pub name: String,
    pub fn_set_with_params: FnSetWithDom,
    pub line_file_index: Option<(usize, usize)>,
}

pub struct HaveObjEqualStmt {
    pub names: Vec<String>,
    pub param_types: Vec<ParameterType>,
    pub objs_equal_to: Vec<Obj>,
    pub line_file_index: Option<(usize, usize)>,
}

pub struct HaveObjInNonemptySetOrParamTypeStmt {
    pub names: Vec<String>,
    pub param_types: Vec<ParameterType>,
    pub line_file_index: Option<(usize, usize)>,
}

pub struct DefLetStmt {
    pub names: Vec<String>,
    pub param_types: Vec<ParameterType>,
    pub facts: Vec<Fact>,
    pub line_file_index: Option<(usize, usize)>,
}

pub struct DefPropStmt {
    pub name: String,
    pub params_def_with_type: Vec<ParamDefWithParamTypeAndProperty>,
    pub iff_facts: Option<Vec<Fact>>,
    pub line_file_index: Option<(usize, usize)>,
}

impl fmt::Display for DefStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DefStmt::DefLetStmt(def_let_stmt) => write!(f, "{}", def_let_stmt),
            DefStmt::DefPropStmt(def_prop_stmt) => write!(f, "{}", def_prop_stmt),
            DefStmt::HaveObjInNonemptySetStmt(have_obj_in_nonempty_set_stmt) => write!(f, "{}", have_obj_in_nonempty_set_stmt),
            DefStmt::HaveObjEqualStmt(have_obj_equal_stmt) => write!(f, "{}", have_obj_equal_stmt),
            DefStmt::LetFnStmt(let_fn_stmt) => write!(f, "{}", let_fn_stmt),
            DefStmt::HaveObjStStmt(have_obj_st_stmt) => write!(f, "{}", have_obj_st_stmt),
            DefStmt::HaveFnEqualStmt(have_fn_equal_stmt) => write!(f, "{}", have_fn_equal_stmt),
            DefStmt::HaveFnEqualCaseByCaseStmt(have_fn_equal_case_by_case_stmt) => write!(f, "{}", have_fn_equal_case_by_case_stmt),
            DefStmt::DefSetTemplateStmt(def_set_template_stmt) => write!(f, "{}", def_set_template_stmt),
            DefStmt::DefineAlgorithmStmt(define_algorithm_stmt) => write!(f, "{}", define_algorithm_stmt),
        }
    }
}

impl DefPropStmt {
    pub fn new(name: String, params_def_with_type: Vec<ParamDefWithParamTypeAndProperty>, iff_facts: Option<Vec<Fact>>, line_file_index: Option<(usize, usize)>) -> Self {
        DefPropStmt { name, params_def_with_type, iff_facts, line_file_index }
    }
}

impl fmt::Display for DefPropStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.iff_facts {
            Some(iff_facts) => write!(f, "{} {}{}{}\n{}", PROP, self.name, braced_vec_to_string(&self.params_def_with_type), COLON,  vec_to_string_add_four_spaces_at_beginning_of_each_line(&iff_facts, 1)),
            None => write!(f, "{} {}{}", PROP, self.name, braced_vec_to_string(&self.params_def_with_type)),
        }
    }
}

impl DefLetStmt {
    pub fn new(names: Vec<String>, param_types: Vec<ParameterType>, facts: Vec<Fact>, line_file_index: Option<(usize, usize)>) -> Self {
        DefLetStmt { names, param_types, facts, line_file_index }
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
    pub fn line_file(&self) -> Option<(usize, usize)> {
        match self {
            DefStmt::DefLetStmt(def_let_stmt) => def_let_stmt.line_file_index,
            DefStmt::DefPropStmt(def_prop_stmt) => def_prop_stmt.line_file_index,
            DefStmt::HaveObjInNonemptySetStmt(have_obj_in_nonempty_set_stmt) => have_obj_in_nonempty_set_stmt.line_file_index,
            DefStmt::HaveObjEqualStmt(have_obj_equal_stmt) => have_obj_equal_stmt.line_file_index,
            DefStmt::LetFnStmt(let_fn_stmt) => let_fn_stmt.line_file_index,
            DefStmt::HaveObjStStmt(have_obj_st_stmt) => have_obj_st_stmt.line_file_index,
            DefStmt::HaveFnEqualStmt(have_fn_equal_stmt) => have_fn_equal_stmt.line_file_index,
            DefStmt::HaveFnEqualCaseByCaseStmt(have_fn_equal_case_by_case_stmt) => have_fn_equal_case_by_case_stmt.line_file_index,
            DefStmt::DefSetTemplateStmt(def_set_template_stmt) => def_set_template_stmt.line_file_index,
            DefStmt::DefineAlgorithmStmt(define_algorithm_stmt) => define_algorithm_stmt.line_file_index,
        }
    }
}

impl HaveObjInNonemptySetOrParamTypeStmt {
    pub fn new(names: Vec<String>, param_types: Vec<ParameterType>, line_file_index: Option<(usize, usize)>) -> Self {
        HaveObjInNonemptySetOrParamTypeStmt { names, param_types, line_file_index }
    }
}

impl fmt::Display for HaveObjInNonemptySetOrParamTypeStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}", HAVE, vec_pair_to_string(&self.names, &self.param_types))
    }
}

impl HaveObjEqualStmt {
    pub fn new(names: Vec<String>, param_types: Vec<ParameterType>, objs_equal_to: Vec<Obj>, line_file_index: Option<(usize, usize)>) -> Self {
        HaveObjEqualStmt { names, param_types, objs_equal_to, line_file_index }
    }
}

impl fmt::Display for HaveObjEqualStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {} {} {}", HAVE, vec_pair_to_string(&self.names, &self.param_types), EQUAL, vec_to_string_join_by_comma(&self.objs_equal_to))
    }
}

impl LetFnStmt {
    pub fn new(name: String, fn_set_with_params: FnSetWithDom, line_file_index: Option<(usize, usize)>) -> Self {
        LetFnStmt { name, fn_set_with_params, line_file_index }
    }
}

fn multiple_line_fn_stmt_str(name: &String, fn_set_with_params: &FnSetWithDom) -> String {
    let dom_facts = &fn_set_with_params.dom_facts;
    let ret_set = &fn_set_with_params.ret_set;
    
    let header = format!("{}{}{}{}", name, braced_vec_to_string(&fn_set_with_params.params_def_with_set), ret_set, COLON);
    match dom_facts.is_empty() {
        true => format!("{}\n{}{}", header, add_four_spaces_at_beginning(RIGHT_ARROW, 1), COLON),
        false => format!("{}\n{}{}\n{}", header, add_four_spaces_at_beginning(DOM, 1), COLON, vec_to_string_add_four_spaces_at_beginning_of_each_line(dom_facts, 2)),
    }
}

impl fmt::Display for LetFnStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}{}\n{}", LET, FN, COLON, to_string_and_add_four_spaces_at_beginning_of_each_line(&multiple_line_fn_stmt_str(&self.name, &self.fn_set_with_params), 1))
    }
}

impl HaveObjStStmt {
    pub fn new(exist_fact_in_have_obj_st: TrueExistFact, line_file_index: Option<(usize, usize)>) -> Self {
        HaveObjStStmt { exist_fact_in_have_obj_st, line_file_index }
    }
}

impl fmt::Display for HaveObjStStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}", HAVE, self.exist_fact_in_have_obj_st.exist_fact_string_without_exist_as_prefix())
    }
}

impl HaveFnEqualStmt {
    pub fn new(name: String, fn_set_with_params: FnSetWithDom, equal_to: Obj, line_file_index: Option<(usize, usize)>) -> Self {
        HaveFnEqualStmt { name, fn_set_with_params, equal_to, line_file_index }
    }
}

impl fmt::Display for HaveFnEqualStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {} {} {}", HAVE, self.fn_set_with_params.with_keyword_fn_with_name_to_string(Some(&self.name)), EQUAL, self.equal_to)
    }
}


impl fmt::Display for HaveFnEqualCaseByCaseStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let cases_and_proofs = self.cases.iter().enumerate().map(|(i, case)| {
            to_string_and_add_four_spaces_at_beginning_of_each_line(&format!("{} {}{} {}{} {} {}", CASE, case, COMMA, self.name, braced_vec_to_string(&self.fn_set_with_params.params()), EQUAL, self.equal_tos[i]),1)
        }).collect::<Vec<String>>();
        
        write!(f, "{} {} {}{}\n{}", HAVE, self.fn_set_with_params, EQUAL, COLON, vec_to_string_with_sep(&cases_and_proofs, "\n"))
    }
}

impl HaveFnEqualCaseByCaseStmt {
    pub fn new(name: String, fn_set_with_params: FnSetWithDom, cases: Vec<AndFactOrSpecFact>, equal_tos: Vec<Obj>, line_file_index: Option<(usize, usize)>) -> Self {
        HaveFnEqualCaseByCaseStmt { name, fn_set_with_params, cases, equal_tos, line_file_index }
    }
}

impl DefSetTemplateStmt {
    pub fn new(name: String, params_def_with_type: Vec<ParamDefWithParamTypeAndProperty>, dom_facts: Vec<OrFactOrAndFactOrSpecFact>, equal_to: Obj, line_file_index: Option<(usize, usize)>) -> Self {
        DefSetTemplateStmt { name, params_def_with_type, dom_facts, equal_to, line_file_index }
    }
}

impl fmt::Display for DefSetTemplateStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}{}{} {} {}{} {} {}", SET_TEMPLATE, self.name,LEFT_BRACE, vec_to_string_join_by_comma(&self.params_def_with_type), COLON, vec_to_string_join_by_comma(&self.dom_facts), RIGHT_BRACE, EQUAL, self.equal_to)
    }
}