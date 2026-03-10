use crate::fact::OrFactOrAndFactOrSpecFact;
use super::parameter_type_and_property::ParamDefWithParamType;
use crate::fact::Fact;
use crate::obj::Obj;
use std::fmt;
use crate::common::keywords::{CASE, COLON, COMMA, EQUAL, EQUIVALENT_SIGN, HAVE, LEFT_BRACE, LET, PROP, RIGHT_BRACE, STRUCT};
use crate::common::helper::{add_four_spaces_at_beginning, braced_vec_to_string, to_string_and_add_four_spaces_at_beginning_of_each_line, vec_to_string_add_four_spaces_at_beginning_of_each_line, vec_to_string_join_by_comma, vec_to_string_with_sep};
use crate::obj::FnSetWithDom;
use crate::fact::AndFactOrChainFactOrAtomicFact;
use crate::fact::TrueExistFact;
use super::define_algorithm_stmt::DefAlgoStmt;

pub enum DefStmt {
    DefLetStmt(DefLetStmt),
    DefPropStmt(DefPropStmt),
    HaveObjInNonemptySetStmt(HaveObjInNonemptySetOrParamTypeStmt),
    HaveObjEqualStmt(HaveObjEqualStmt),
    HaveExistObjStmt(HaveExistObjStmt),
    HaveFnEqualStmt(HaveFnEqualStmt),
    HaveFnEqualCaseByCaseStmt(HaveFnEqualCaseByCaseStmt),
    DefStructStmt(DefStructStmt),
    DefAlgoStmt(DefAlgoStmt),
}

#[derive(Clone)]
pub enum DefStructStmt {
    DefStructWithFieldsStmt(DefStructWithFieldsStmt),
    DefStructWithNoFieldStmt(DefStructWithNoFieldStmt),
}

#[derive(Clone)]
pub struct DefStructWithFieldsStmt {
    pub name: String,
    pub params_def_with_type: Vec<ParamDefWithParamType>,
    pub fields: Vec<(String, OrFactOrAndFactOrSpecFact)>,
    pub facts: Vec<OrFactOrAndFactOrSpecFact>,
    pub line_file_index: Option<(usize, usize)>,
}

#[derive(Clone)]
pub struct DefStructWithNoFieldStmt {
    pub name: String,
    pub params_def_with_type: Vec<ParamDefWithParamType>,
    pub dom_facts: Vec<OrFactOrAndFactOrSpecFact>,
    pub equal_to: Obj,
    pub line_file_index: Option<(usize, usize)>,
}

pub struct HaveFnEqualCaseByCaseStmt {
    pub name: String,
    pub fn_set_with_params: FnSetWithDom,
    pub cases: Vec<AndFactOrChainFactOrAtomicFact>,
    pub equal_tos: Vec<Obj>,
    pub line_file_index: Option<(usize, usize)>,
}

pub struct HaveFnEqualStmt {
    pub name: String,
    pub fn_set_with_params: FnSetWithDom,
    pub equal_to: Obj,
    pub line_file_index: Option<(usize, usize)>,
}

pub struct HaveExistObjStmt {
    pub exist_fact_in_have_obj_st: TrueExistFact,
    pub line_file_index: Option<(usize, usize)>,
}

pub struct HaveObjEqualStmt {
    pub param_def: Vec<ParamDefWithParamType>,
    pub objs_equal_to: Vec<Obj>,
    pub line_file_index: Option<(usize, usize)>,
}

pub struct HaveObjInNonemptySetOrParamTypeStmt {
    pub param_def: Vec<ParamDefWithParamType>,
    pub line_file_index: Option<(usize, usize)>,
}

pub struct DefLetStmt {
    pub param_def: Vec<ParamDefWithParamType>,
    pub facts: Vec<Fact>,
    pub line_file_index: Option<(usize, usize)>,
}

#[derive(Clone)]
pub struct DefPropStmt {
    pub name: String,
    pub params_def_with_type: Vec<ParamDefWithParamType>,
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
            DefStmt::HaveExistObjStmt(have_obj_st_stmt) => write!(f, "{}", have_obj_st_stmt),
            DefStmt::HaveFnEqualStmt(have_fn_equal_stmt) => write!(f, "{}", have_fn_equal_stmt),
            DefStmt::HaveFnEqualCaseByCaseStmt(have_fn_equal_case_by_case_stmt) => write!(f, "{}", have_fn_equal_case_by_case_stmt),
            DefStmt::DefStructStmt(def_struct_stmt) => write!(f, "{}", def_struct_stmt),
            DefStmt::DefAlgoStmt(define_algorithm_stmt) => write!(f, "{}", define_algorithm_stmt),
        }
    }
}

impl fmt::Display for DefStructStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DefStructStmt::DefStructWithFieldsStmt(x) => write!(f, "{}", x),
            DefStructStmt::DefStructWithNoFieldStmt(x) => write!(f, "{}", x),
        }
    }
}

impl DefStructStmt {
    pub fn name(&self) -> &str {
        match self {
            DefStructStmt::DefStructWithFieldsStmt(x) => &x.name,
            DefStructStmt::DefStructWithNoFieldStmt(x) => &x.name,
        }
    }

    pub fn line_file_index(&self) -> Option<(usize, usize)> {
        match self {
            DefStructStmt::DefStructWithFieldsStmt(x) => x.line_file_index,
            DefStructStmt::DefStructWithNoFieldStmt(x) => x.line_file_index,
        }
    }
}

impl fmt::Display for DefStructWithFieldsStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // 格式: struct name(params): \n  field1 or1 \n  field2 or2 \n  <=>: \n  facts...
        let fields_str: String = self.fields.iter().map(|(name, or_val)| format!("{} {}", name, or_val)).collect::<Vec<_>>().join("\n");
        let fields_indented = to_string_and_add_four_spaces_at_beginning_of_each_line(&fields_str, 1);
        let equiv_line = add_four_spaces_at_beginning(&format!("{}{}", EQUIVALENT_SIGN, COLON), 1);
        let facts_indented = vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.facts, 1);
        write!(f, "{} {}{}{}{} {}\n{}\n{}\n{}", STRUCT, self.name, LEFT_BRACE, vec_to_string_join_by_comma(&self.params_def_with_type), RIGHT_BRACE, COLON, fields_indented, equiv_line, facts_indented)
    }
}

impl DefPropStmt {
    pub fn new(name: String, params_def_with_type: Vec<ParamDefWithParamType>, iff_facts: Option<Vec<Fact>>, line_file_index: Option<(usize, usize)>) -> Self {
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
    pub fn new(param_def: Vec<ParamDefWithParamType>, facts: Vec<Fact>, line_file_index: Option<(usize, usize)>) -> Self {
        DefLetStmt { param_def, facts, line_file_index }
    }
}

impl fmt::Display for DefLetStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let param_str = vec_to_string_with_sep(&self.param_def, ", ");
        match self.facts.len() {
            0 => write!(f, "{} {}", LET, param_str),
            _ => write!(f, "{} {}{}\n{}", LET, param_str, COLON, vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.facts, 1)),
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
            DefStmt::HaveExistObjStmt(have_obj_st_stmt) => have_obj_st_stmt.line_file_index,
            DefStmt::HaveFnEqualStmt(have_fn_equal_stmt) => have_fn_equal_stmt.line_file_index,
            DefStmt::HaveFnEqualCaseByCaseStmt(have_fn_equal_case_by_case_stmt) => have_fn_equal_case_by_case_stmt.line_file_index,
            DefStmt::DefStructStmt(def_struct_stmt) => def_struct_stmt.line_file_index(),
            DefStmt::DefAlgoStmt(define_algorithm_stmt) => define_algorithm_stmt.line_file_index,
        }
    }
}

impl HaveObjInNonemptySetOrParamTypeStmt {
    pub fn new(param_def: Vec<ParamDefWithParamType>, line_file_index: Option<(usize, usize)>) -> Self {
        HaveObjInNonemptySetOrParamTypeStmt { param_def, line_file_index }
    }
}

impl fmt::Display for HaveObjInNonemptySetOrParamTypeStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}", HAVE, vec_to_string_join_by_comma(&self.param_def))
    }
}

impl HaveObjEqualStmt {
    pub fn new(param_def: Vec<ParamDefWithParamType>, objs_equal_to: Vec<Obj>, line_file_index: Option<(usize, usize)>) -> Self {
        HaveObjEqualStmt { param_def, objs_equal_to, line_file_index }
    }
}

impl fmt::Display for HaveObjEqualStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {} {} {}", HAVE, vec_to_string_with_sep(&self.param_def, ", "), EQUAL, vec_to_string_join_by_comma(&self.objs_equal_to))
    }
}

impl HaveExistObjStmt {
    pub fn new(exist_fact_in_have_obj_st: TrueExistFact, line_file_index: Option<(usize, usize)>) -> Self {
        HaveExistObjStmt { exist_fact_in_have_obj_st, line_file_index }
    }
}

impl fmt::Display for HaveExistObjStmt {
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
    pub fn new(name: String, fn_set_with_params: FnSetWithDom, cases: Vec<AndFactOrChainFactOrAtomicFact>, equal_tos: Vec<Obj>, line_file_index: Option<(usize, usize)>) -> Self {
        HaveFnEqualCaseByCaseStmt { name, fn_set_with_params, cases, equal_tos, line_file_index }
    }
}

impl DefStructWithNoFieldStmt {
    pub fn new(name: String, params_def_with_type: Vec<ParamDefWithParamType>, dom_facts: Vec<OrFactOrAndFactOrSpecFact>, equal_to: Obj, line_file_index: Option<(usize, usize)>) -> Self {
        DefStructWithNoFieldStmt { name, params_def_with_type, dom_facts, equal_to, line_file_index }
    }
}

impl fmt::Display for DefStructWithNoFieldStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}{}{} {} {}{} {} {}", STRUCT, self.name,LEFT_BRACE, vec_to_string_join_by_comma(&self.params_def_with_type), COLON, vec_to_string_join_by_comma(&self.dom_facts), RIGHT_BRACE, EQUAL, self.equal_to)
    }
}

impl DefStructWithFieldsStmt {
    pub fn new(name: String, params_def_with_type: Vec<ParamDefWithParamType>, fields: Vec<(String, OrFactOrAndFactOrSpecFact)>, facts: Vec<OrFactOrAndFactOrSpecFact>, line_file_index: Option<(usize, usize)>) -> Self {
        DefStructWithFieldsStmt { name, params_def_with_type, fields, facts, line_file_index }
    }
}

