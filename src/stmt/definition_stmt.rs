use crate::{
    prelude::*,
    stmt::parameter_def::{ParamDefWithStructFieldType, StructFieldType},
};
use std::fmt;

#[derive(Clone)]
pub struct DefAbstractPropStmt {
    pub name: String,
    pub params: Vec<String>,
    pub line_file: LineFile,
}

impl DefAbstractPropStmt {
    pub fn new(name: String, params: Vec<String>, line_file: LineFile) -> Self {
        DefAbstractPropStmt {
            name,
            params,
            line_file,
        }
    }
}

#[derive(Clone)]
pub struct DefParamTypeStructStmt {
    pub name: String,
    pub param_defs: Vec<ParamDefWithStructFieldType>,
    pub dom_facts: Vec<OrAndChainAtomicFact>,
    pub fields: Vec<(String, StructFieldType)>,
    pub facts: Vec<OrAndChainAtomicFact>,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct DefFamilyStmt {
    pub name: String,
    pub params_def_with_type: Vec<ParamDefWithParamType>,
    pub dom_facts: Vec<OrAndChainAtomicFact>,
    pub equal_to: Obj,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct HaveFnEqualCaseByCaseStmt {
    pub name: String,
    pub fn_set_with_params: FnSetWithParams,
    pub cases: Vec<AndChainAtomicFact>,
    pub equal_tos: Vec<Obj>,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct HaveFnEqualStmt {
    pub name: String,
    pub fn_set_with_params: FnSetWithParams,
    pub equal_to: Obj,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct HaveExistObjStmt {
    pub equal_tos: Vec<String>,
    pub exist_fact_in_have_obj_st: ExistFact,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct HaveObjEqualStmt {
    pub param_def: Vec<ParamDefWithParamType>,
    pub objs_equal_to: Vec<Obj>,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct HaveObjInNonemptySetOrParamTypeStmt {
    pub param_def: Vec<ParamDefWithParamType>,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct DefLetStmt {
    pub param_def: Vec<ParamDefWithParamType>,
    pub facts: Vec<Fact>,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct DefPropStmt {
    pub name: String,
    pub params_def_with_type: Vec<ParamDefWithParamType>,
    pub iff_facts: Vec<Fact>,
    pub line_file: LineFile,
}

impl fmt::Display for DefAbstractPropStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} {}{}{}{}",
            ABSTRACT_PROP,
            self.name,
            LEFT_BRACE,
            vec_to_string_join_by_comma(&self.params),
            RIGHT_BRACE
        )
    }
}

impl fmt::Display for DefParamTypeStructStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // 格式: struct name(params): \n  field1 or1 \n  field2 or2 \n  <=>: \n  facts...
        // 解析器会为每个类型参数自动前置一条 field；Display 只还原用户写出来的字段。
        let implicit_prefix_len = ParamDefWithStructFieldType::number_of_params(&self.param_defs);
        let fields_str: String = self
            .fields
            .iter()
            .skip(implicit_prefix_len)
            .map(|(name, or_val)| format!("{} {}", name, or_val))
            .collect::<Vec<_>>()
            .join("\n");
        let fields_indented =
            to_string_and_add_four_spaces_at_beginning_of_each_line(&fields_str, 1);
        let equiv_line = add_four_spaces_at_beginning(format!("{}{}", EQUIVALENT_SIGN, COLON), 1);
        let facts_indented = vec_to_string_add_four_spaces_at_beginning_of_each_line(
            &self.facts.iter().skip(implicit_prefix_len).cloned().collect(),
            1,
        );
        write!(
            f,
            "{} {}{}{}{} {}\n{}\n{}\n{}",
            STRUCT,
            self.name,
            LEFT_BRACE,
            vec_to_string_join_by_comma(&self.param_defs),
            RIGHT_BRACE,
            COLON,
            fields_indented,
            equiv_line,
            facts_indented
        )
    }
}

impl DefPropStmt {
    pub fn new(
        name: String,
        params_def_with_type: Vec<ParamDefWithParamType>,
        iff_facts: Vec<Fact>,
        line_file: LineFile,
    ) -> Self {
        DefPropStmt {
            name,
            params_def_with_type,
            iff_facts,
            line_file,
        }
    }
}

impl fmt::Display for DefPropStmt {
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
        line_file: LineFile,
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
    pub fn new(param_def: Vec<ParamDefWithParamType>, line_file: LineFile) -> Self {
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
        line_file: LineFile,
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
        line_file: LineFile,
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
            "{} {} {} {} {}",
            HAVE,
            BY,
            self.exist_fact_in_have_obj_st,
            COLON,
            vec_to_string_join_by_comma(&self.equal_tos),
        )
    }
}

impl HaveFnEqualStmt {
    pub fn new(
        name: String,
        fn_set_with_params: FnSetWithParams,
        equal_to: Obj,
        line_file: LineFile,
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
        line_file: LineFile,
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

impl DefFamilyStmt {
    pub fn new(
        name: String,
        params_def_with_type: Vec<ParamDefWithParamType>,
        dom_facts: Vec<OrAndChainAtomicFact>,
        equal_to: Obj,
        line_file: LineFile,
    ) -> Self {
        DefFamilyStmt {
            name,
            params_def_with_type,
            dom_facts,
            equal_to,
            line_file,
        }
    }
}

impl fmt::Display for DefFamilyStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} {}{}{} {} {}{} {} {}",
            FAMILY,
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

impl DefParamTypeStructStmt {
    pub fn new(
        name: String,
        param_defs: Vec<ParamDefWithStructFieldType>,
        dom_facts: Vec<OrAndChainAtomicFact>,
        fields: Vec<(String, StructFieldType)>,
        facts: Vec<OrAndChainAtomicFact>,
        line_file: LineFile,
    ) -> Self {
        DefParamTypeStructStmt {
            name,
            param_defs,
            dom_facts,
            fields,
            facts,
            line_file,
        }
    }
}

impl DefParamTypeStructStmt {
    pub fn number_of_params(&self) -> usize {
        ParamDefWithStructFieldType::number_of_params(&self.param_defs)
    }

    /// 按定义顺序展开所有类型形参名（与 `struct T(...)` 中参数顺序一致）。
    pub fn get_params(&self) -> Vec<String> {
        ParamDefWithStructFieldType::collect_param_names(&self.param_defs)
    }
}