use super::parameter_def::ParamDefWithParamType;
use crate::common::helper::{
    add_four_spaces_at_beginning, brace_vec_colon_vec_to_string, braced_vec_to_string,
    to_string_and_add_four_spaces_at_beginning_of_each_line,
    vec_to_string_add_four_spaces_at_beginning_of_each_line, vec_to_string_join_by_comma,
    vec_to_string_with_sep,
};
use crate::common::keywords::{
    CASE, COLON, COMMA, EQUAL, EQUIVALENT_SIGN, FN_FOR_FN_WITH_PARAMS, HAVE, LEFT_BRACE, LET, PROP,
    RIGHT_BRACE, STRUCT,
};
use crate::fact::AndChainAtomicFact;
use crate::fact::ExistFact;
use crate::fact::Fact;
use crate::fact::OrAndChainAtomicFact;
use crate::obj::FnSetWithParams;
use crate::obj::Obj;
use std::fmt;

#[derive(Clone)]
pub struct DefPropWithoutMeaningStmt {
    pub name: String,
    pub params: Vec<String>,
    pub line_file: (usize, usize),
}

impl DefPropWithoutMeaningStmt {
    pub fn new(name: String, params: Vec<String>, line_file: (usize, usize)) -> Self {
        DefPropWithoutMeaningStmt {
            name,
            params,
            line_file,
        }
    }
}

#[derive(Clone)]
pub struct DefStructWithFieldsStmt {
    pub name: String,
    pub params_def_with_type: Vec<ParamDefWithParamType>,
    pub fields: Vec<(String, OrAndChainAtomicFact)>,
    pub facts: Vec<OrAndChainAtomicFact>,
    pub line_file: (usize, usize),
}

#[derive(Clone)]
pub struct DefStructWithNoFieldStmt {
    pub name: String,
    pub params_def_with_type: Vec<ParamDefWithParamType>,
    pub dom_facts: Vec<OrAndChainAtomicFact>,
    pub equal_to: Obj,
    pub line_file: (usize, usize),
}

#[derive(Clone)]
pub struct HaveFnEqualCaseByCaseStmt {
    pub name: String,
    pub fn_set_with_params: FnSetWithParams,
    pub cases: Vec<AndChainAtomicFact>,
    pub equal_tos: Vec<Obj>,
    pub line_file: (usize, usize),
}

#[derive(Clone)]
pub struct HaveFnEqualStmt {
    pub name: String,
    pub fn_set_with_params: FnSetWithParams,
    pub equal_to: Obj,
    pub line_file: (usize, usize),
}

#[derive(Clone)]
pub struct HaveExistObjStmt {
    pub equal_tos: Vec<String>,
    pub exist_fact_in_have_obj_st: ExistFact,
    pub line_file: (usize, usize),
}

#[derive(Clone)]
pub struct HaveObjEqualStmt {
    pub param_def: Vec<ParamDefWithParamType>,
    pub objs_equal_to: Vec<Obj>,
    pub line_file: (usize, usize),
}

#[derive(Clone)]
pub struct HaveObjInNonemptySetOrParamTypeStmt {
    pub param_def: Vec<ParamDefWithParamType>,
    pub line_file: (usize, usize),
}

#[derive(Clone)]
pub struct DefLetStmt {
    pub param_def: Vec<ParamDefWithParamType>,
    pub facts: Vec<Fact>,
    pub line_file: (usize, usize),
}

#[derive(Clone)]
pub struct DefPropWithMeaningStmt {
    pub name: String,
    pub params_def_with_type: Vec<ParamDefWithParamType>,
    pub iff_facts: Vec<Fact>,
    pub line_file: (usize, usize),
}

impl fmt::Display for DefPropWithoutMeaningStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} {}{}{}{}",
            PROP,
            self.name,
            LEFT_BRACE,
            vec_to_string_join_by_comma(&self.params),
            RIGHT_BRACE
        )
    }
}

impl fmt::Display for DefStructWithFieldsStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // 格式: struct name(params): \n  field1 or1 \n  field2 or2 \n  <=>: \n  facts...
        let fields_str: String = self
            .fields
            .iter()
            .map(|(name, or_val)| format!("{} {}", name, or_val))
            .collect::<Vec<_>>()
            .join("\n");
        let fields_indented =
            to_string_and_add_four_spaces_at_beginning_of_each_line(&fields_str, 1);
        let equiv_line = add_four_spaces_at_beginning(format!("{}{}", EQUIVALENT_SIGN, COLON), 1);
        let facts_indented =
            vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.facts, 1);
        write!(
            f,
            "{} {}{}{}{} {}\n{}\n{}\n{}",
            STRUCT,
            self.name,
            LEFT_BRACE,
            vec_to_string_join_by_comma(&self.params_def_with_type),
            RIGHT_BRACE,
            COLON,
            fields_indented,
            equiv_line,
            facts_indented
        )
    }
}

impl DefPropWithMeaningStmt {
    pub fn new(
        name: String,
        params_def_with_type: Vec<ParamDefWithParamType>,
        iff_facts: Vec<Fact>,
        line_file: (usize, usize),
    ) -> Self {
        DefPropWithMeaningStmt {
            name,
            params_def_with_type,
            iff_facts,
            line_file,
        }
    }
}

impl fmt::Display for DefPropWithMeaningStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.iff_facts.len() {
            0 => write!(
                f,
                "{} {}{}",
                PROP,
                self.name,
                braced_vec_to_string(&self.params_def_with_type)
            ),
            _ => write!(
                f,
                "{} {}{}{}\n{}",
                PROP,
                self.name,
                braced_vec_to_string(&self.params_def_with_type),
                COLON,
                vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.iff_facts, 1)
            ),
        }
    }
}

impl DefLetStmt {
    pub fn new(
        param_def: Vec<ParamDefWithParamType>,
        facts: Vec<Fact>,
        line_file: (usize, usize),
    ) -> Self {
        DefLetStmt {
            param_def,
            facts,
            line_file,
        }
    }
}

impl fmt::Display for DefLetStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let param_str = vec_to_string_with_sep(&self.param_def, ", ".to_string());
        match self.facts.len() {
            0 => write!(f, "{} {}", LET, param_str),
            _ => write!(
                f,
                "{} {}{}\n{}",
                LET,
                param_str,
                COLON,
                vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.facts, 1)
            ),
        }
    }
}

impl HaveObjInNonemptySetOrParamTypeStmt {
    pub fn new(param_def: Vec<ParamDefWithParamType>, line_file: (usize, usize)) -> Self {
        HaveObjInNonemptySetOrParamTypeStmt {
            param_def,
            line_file,
        }
    }
}

impl fmt::Display for HaveObjInNonemptySetOrParamTypeStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} {}",
            HAVE,
            vec_to_string_join_by_comma(&self.param_def)
        )
    }
}

impl HaveObjEqualStmt {
    pub fn new(
        param_def: Vec<ParamDefWithParamType>,
        objs_equal_to: Vec<Obj>,
        line_file: (usize, usize),
    ) -> Self {
        HaveObjEqualStmt {
            param_def,
            objs_equal_to,
            line_file,
        }
    }
}

impl fmt::Display for HaveObjEqualStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} {} {} {}",
            HAVE,
            vec_to_string_with_sep(&self.param_def, ", ".to_string()),
            EQUAL,
            vec_to_string_join_by_comma(&self.objs_equal_to)
        )
    }
}

impl HaveExistObjStmt {
    pub fn new(
        equal_tos: Vec<String>,
        exist_fact_in_have_obj_st: ExistFact,
        line_file: (usize, usize),
    ) -> Self {
        HaveExistObjStmt {
            equal_tos,
            exist_fact_in_have_obj_st,
            line_file,
        }
    }
}

impl fmt::Display for HaveExistObjStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} {} {} {}",
            HAVE,
            vec_to_string_join_by_comma(&self.equal_tos),
            COLON,
            self.exist_fact_in_have_obj_st
                .exist_fact_string_without_exist_as_prefix()
        )
    }
}

impl HaveFnEqualStmt {
    pub fn new(
        name: String,
        fn_set_with_params: FnSetWithParams,
        equal_to: Obj,
        line_file: (usize, usize),
    ) -> Self {
        HaveFnEqualStmt {
            name,
            fn_set_with_params,
            equal_to,
            line_file,
        }
    }
}

impl fmt::Display for HaveFnEqualStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} {} {}{} {} {}",
            HAVE,
            FN_FOR_FN_WITH_PARAMS,
            self.name,
            brace_vec_colon_vec_to_string(
                &self.fn_set_with_params.params_def_with_set,
                &self.fn_set_with_params.dom_facts
            ),
            EQUAL,
            self.equal_to
        )
    }
}

impl fmt::Display for HaveFnEqualCaseByCaseStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let cases_and_proofs = self
            .cases
            .iter()
            .enumerate()
            .map(|(i, case)| {
                to_string_and_add_four_spaces_at_beginning_of_each_line(
                    &format!(
                        "{} {}{} {}{} {} {}",
                        CASE,
                        case,
                        COMMA,
                        self.name,
                        braced_vec_to_string(&self.fn_set_with_params.params()),
                        EQUAL,
                        self.equal_tos[i]
                    ),
                    1,
                )
            })
            .collect::<Vec<String>>();

        write!(
            f,
            "{} {} {}{} {} {}\n{}",
            HAVE,
            FN_FOR_FN_WITH_PARAMS,
            self.name,
            brace_vec_colon_vec_to_string(
                &self.fn_set_with_params.params_def_with_set,
                &self.fn_set_with_params.dom_facts
            ),
            EQUAL,
            COLON,
            vec_to_string_with_sep(&cases_and_proofs, "\n".to_string())
        )
    }
}

impl HaveFnEqualCaseByCaseStmt {
    pub fn new(
        name: String,
        fn_set_with_params: FnSetWithParams,
        cases: Vec<AndChainAtomicFact>,
        equal_tos: Vec<Obj>,
        line_file: (usize, usize),
    ) -> Self {
        HaveFnEqualCaseByCaseStmt {
            name,
            fn_set_with_params,
            cases,
            equal_tos,
            line_file,
        }
    }
}

impl DefStructWithNoFieldStmt {
    pub fn new(
        name: String,
        params_def_with_type: Vec<ParamDefWithParamType>,
        dom_facts: Vec<OrAndChainAtomicFact>,
        equal_to: Obj,
        line_file: (usize, usize),
    ) -> Self {
        DefStructWithNoFieldStmt {
            name,
            params_def_with_type,
            dom_facts,
            equal_to,
            line_file,
        }
    }
}

impl fmt::Display for DefStructWithNoFieldStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} {}{}{} {} {}{} {} {}",
            STRUCT,
            self.name,
            LEFT_BRACE,
            vec_to_string_join_by_comma(&self.params_def_with_type),
            COLON,
            vec_to_string_join_by_comma(&self.dom_facts),
            RIGHT_BRACE,
            EQUAL,
            self.equal_to
        )
    }
}

impl DefStructWithFieldsStmt {
    pub fn new(
        name: String,
        params_def_with_type: Vec<ParamDefWithParamType>,
        fields: Vec<(String, OrAndChainAtomicFact)>,
        facts: Vec<OrAndChainAtomicFact>,
        line_file: (usize, usize),
    ) -> Self {
        DefStructWithFieldsStmt {
            name,
            params_def_with_type,
            fields,
            facts,
            line_file,
        }
    }
}
