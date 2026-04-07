use crate::{
    prelude::*,
    stmt::parameter_def::{ParamGroupWithStructFieldType, StructFieldType},
};
use std::fmt;

/// `have fn by induc from`：前若干条须为 `param = from`, `param = from + 1`, …；最后一条须为
/// `param = param_2 + len(special_cases_equal_tos)`（`param_2` 与 `from` 同侧），且要么 `: obj`（`last_case_equal_to`），要么无右值而
/// 跟子 `case` 列表（`last_case_cases`）。
#[derive(Clone)]
pub struct HaveFnByInducStmt {
    pub induc_from: Obj,
    pub name: String,
    pub fn_set: FnSet,
    pub special_cases_equal_tos: Vec<Obj>,
    pub last_case_equal_to: Option<Obj>,
    pub last_case_cases: Option<Vec<(AndChainAtomicFact, Obj)>>,
    pub line_file: LineFile,
}

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
pub struct DefStructStmt {
    pub name: String,
    pub param_defs: Vec<ParamGroupWithStructFieldType>,
    pub dom_facts: Vec<OrAndChainAtomicFact>,
    pub fields: Vec<(String, StructFieldType)>,
    pub facts: Vec<OrAndChainAtomicFact>,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct DefFamilyStmt {
    pub name: String,
    pub params_def_with_type: Vec<ParamGroupWithParamType>,
    pub dom_facts: Vec<OrAndChainAtomicFact>,
    pub equal_to: Obj,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct HaveFnEqualCaseByCaseStmt {
    pub name: String,
    pub fn_set_with_params: FnSet,
    pub cases: Vec<AndChainAtomicFact>,
    pub equal_tos: Vec<Obj>,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct HaveFnEqualStmt {
    pub name: String,
    pub fn_set_with_params: FnSet,
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
    pub param_def: Vec<ParamGroupWithParamType>,
    pub objs_equal_to: Vec<Obj>,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct HaveObjInNonemptySetOrParamTypeStmt {
    pub param_def: Vec<ParamGroupWithParamType>,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct DefLetStmt {
    pub param_def: Vec<ParamGroupWithParamType>,
    pub facts: Vec<Fact>,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct DefPropStmt {
    pub name: String,
    pub params_def_with_type: Vec<ParamGroupWithParamType>,
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

impl fmt::Display for DefStructStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // 格式: struct name(params): \n  field1 or1 \n  field2 or2 \n  <=>: \n  facts...
        // 解析器会为每个类型参数自动前置一条 field；Display 只还原用户写出来的字段。
        let implicit_prefix_len = ParamGroupWithStructFieldType::number_of_params(&self.param_defs);
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
            &self
                .facts
                .iter()
                .skip(implicit_prefix_len)
                .cloned()
                .collect(),
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
        params_def_with_type: Vec<ParamGroupWithParamType>,
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
        param_def: Vec<ParamGroupWithParamType>,
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
    pub fn new(param_def: Vec<ParamGroupWithParamType>, line_file: LineFile) -> Self {
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
        param_def: Vec<ParamGroupWithParamType>,
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
        fn_set_with_params: FnSet,
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
            FN,
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
            FN,
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
        fn_set_with_params: FnSet,
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

impl fmt::Display for HaveFnByInducStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let flat = self.to_have_fn_equal_case_by_case_stmt();
        let cases_and_proofs = flat
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
                        braced_vec_to_string(&self.fn_set.params()),
                        EQUAL,
                        flat.equal_tos[i]
                    ),
                    1,
                )
            })
            .collect::<Vec<String>>();

        write!(
            f,
            "{} {} {} {} {} {}{} {}{} {} {}\n{}",
            HAVE,
            FN,
            BY,
            INDUC,
            FROM,
            self.induc_from,
            COLON,
            self.name,
            brace_vec_colon_vec_to_string(&self.fn_set.params_def_with_set, &self.fn_set.dom_facts),
            EQUAL,
            COLON,
            vec_to_string_with_sep(&cases_and_proofs, "\n".to_string())
        )
    }
}

pub(crate) fn induc_obj_plus_offset(induc_from: &Obj, offset: usize) -> Obj {
    if offset == 0 {
        induc_from.clone()
    } else {
        Obj::Add(Add::new(
            induc_from.clone(),
            Obj::Number(Number::new(offset.to_string())),
        ))
    }
}

fn flatten_and_chain_to_atomic_facts(c: &AndChainAtomicFact) -> Vec<AtomicFact> {
    match c {
        AndChainAtomicFact::AtomicFact(a) => vec![a.clone()],
        AndChainAtomicFact::AndFact(af) => af.facts.clone(),
        AndChainAtomicFact::ChainFact(cf) => cf.facts().unwrap(),
    }
}

fn merge_two_and_chain_clauses(
    a: AndChainAtomicFact,
    b: AndChainAtomicFact,
    line_file: LineFile,
) -> AndChainAtomicFact {
    let mut atoms = flatten_and_chain_to_atomic_facts(&a);
    atoms.extend(flatten_and_chain_to_atomic_facts(&b));
    AndChainAtomicFact::AndFact(AndFact::new(atoms, line_file))
}

impl HaveFnByInducStmt {
    pub fn new(
        name: String,
        fn_set_with_params: FnSet,
        induc_from: Obj,
        special_cases_equal_tos: Vec<Obj>,
        last_case_equal_to: Option<Obj>,
        last_case_cases: Option<Vec<(AndChainAtomicFact, Obj)>>,
        line_file: LineFile,
    ) -> Self {
        HaveFnByInducStmt {
            name,
            fn_set: fn_set_with_params,
            induc_from,
            special_cases_equal_tos,
            last_case_equal_to,
            last_case_cases,
            line_file,
        }
    }

    /// 展开为与旧 `HaveFnEqualCaseByCaseStmt` 兼容的平铺 `case` 列表（归纳步为 `param = from + n` 与可选子条件的合取）。
    pub fn to_have_fn_equal_case_by_case_stmt(&self) -> HaveFnEqualCaseByCaseStmt {
        let line_file = self.line_file.clone();
        let param_name = self.fn_set.params()[0].clone();
        let left_id = Obj::Identifier(Identifier::new(param_name));
        let n = self.special_cases_equal_tos.len();
        let mut cases: Vec<AndChainAtomicFact> = Vec::new();
        let mut equal_tos: Vec<Obj> = Vec::new();
        for i in 0..n {
            let when = AndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(
                left_id.clone(),
                induc_obj_plus_offset(&self.induc_from, i),
                line_file.clone(),
            )));
            cases.push(when);
            equal_tos.push(self.special_cases_equal_tos[i].clone());
        }
        let step = AndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(
            left_id.clone(),
            induc_obj_plus_offset(&self.induc_from, n),
            line_file.clone(),
        )));
        match (&self.last_case_equal_to, &self.last_case_cases) {
            (Some(eq), None) => {
                cases.push(step);
                equal_tos.push(eq.clone());
            }
            (None, Some(last_pairs)) => {
                for (when, eq_to) in last_pairs {
                    let merged = merge_two_and_chain_clauses(
                        step.clone(),
                        when.clone(),
                        line_file.clone(),
                    );
                    cases.push(merged);
                    equal_tos.push(eq_to.clone());
                }
            }
            (None, None) | (Some(_), Some(_)) => {
                unreachable!(
                    "HaveFnByInducStmt: last case must be either `: obj` or nested `case` blocks, not both or neither"
                );
            }
        }
        HaveFnEqualCaseByCaseStmt::new(
            self.name.clone(),
            self.fn_set.clone(),
            cases,
            equal_tos,
            line_file,
        )
    }
}

impl DefFamilyStmt {
    pub fn new(
        name: String,
        params_def_with_type: Vec<ParamGroupWithParamType>,
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

impl DefStructStmt {
    pub fn new(
        name: String,
        param_defs: Vec<ParamGroupWithStructFieldType>,
        dom_facts: Vec<OrAndChainAtomicFact>,
        fields: Vec<(String, StructFieldType)>,
        facts: Vec<OrAndChainAtomicFact>,
        line_file: LineFile,
    ) -> Self {
        DefStructStmt {
            name,
            param_defs,
            dom_facts,
            fields,
            facts,
            line_file,
        }
    }

    pub fn number_of_params(&self) -> usize {
        ParamGroupWithStructFieldType::number_of_params(&self.param_defs)
    }

    /// 按定义顺序展开所有类型形参名（与 `struct T(...)` 中参数顺序一致）。
    pub fn get_params(&self) -> Vec<String> {
        ParamGroupWithStructFieldType::collect_param_names(&self.param_defs)
    }
}
