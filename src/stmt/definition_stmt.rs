use crate::prelude::*;
use crate::stmt::parameter_def::ParamDefWithType;
use std::fmt;

#[derive(Clone)]
pub struct HaveFnByInducCase {
    pub case_fact: AndChainAtomicFact,
    pub body: HaveFnByInducCaseBody,
}

#[derive(Clone)]
pub enum HaveFnByInducCaseBody {
    EqualTo(Obj),
    NestedCases(Vec<HaveFnByInducCase>),
}

// have fn f(a Z, b Z: a >= 0, b >= 0) R
//     by decreasing abs(a) + abs(b) from 0:
//         case b = 0: 0
//         case b > 0: f(a, b - 1) + 1
#[derive(Clone)]
pub struct HaveFnByInducStmt {
    pub name: String,
    pub fn_set_clause: FnSetClause,
    pub measure: Obj,
    pub lower_bound: Obj,
    pub cases: Vec<HaveFnByInducCase>,
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
pub struct DefFamilyStmt {
    pub name: String,
    pub params_def_with_type: ParamDefWithType,
    pub dom_facts: Vec<OrAndChainAtomicFact>,
    pub equal_to: Obj,
    pub line_file: LineFile,
}

/// `have fn` `{ ... }` piece. Parameter sets may depend on earlier parameters; `ret_set` must not
/// cite these parameters.
#[derive(Clone)]
pub struct FnSetClause {
    pub params_def_with_set: ParamDefWithSet,
    pub dom_facts: Vec<OrAndChainAtomicFact>,
    pub ret_set: Obj,
}

impl FnSetClause {
    pub fn new(
        params_def_with_set: impl Into<ParamDefWithSet>,
        dom_facts: Vec<OrAndChainAtomicFact>,
        ret_set: Obj,
    ) -> Result<Self, RuntimeError> {
        let params_def_with_set = params_def_with_set.into();
        params_def_with_set.validate_obj_does_not_cite_params(&ret_set, "function return set")?;
        Ok(FnSetClause {
            params_def_with_set,
            dom_facts,
            ret_set,
        })
    }

    /// Outer `{...}` binders first, then each nested function return `fn` layer, in order.
    /// Used when parsing `have fn ... = rhs` so RHS identifiers match nested return fn-set params.
    pub fn collect_all_param_names_including_nested_ret_fn_sets(&self) -> Vec<String> {
        let mut names = ParamGroupWithSet::collect_param_names(&self.params_def_with_set);
        let mut ret_set = self.ret_set.clone();
        while let Obj::FnSet(inner) = ret_set {
            names.extend(ParamGroupWithSet::collect_param_names(
                &inner.body.params_def_with_set,
            ));
            ret_set = (*inner.body.ret_set).clone();
        }
        names
    }
}

#[derive(Clone)]
pub struct HaveFnEqualCaseByCaseStmt {
    pub name: String,
    pub fn_set_clause: FnSetClause,
    pub cases: Vec<AndChainAtomicFact>,
    pub equal_tos: Vec<Obj>,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct HaveFnEqualStmt {
    pub name: String,
    pub equal_to_anonymous_fn: AnonymousFn,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct HaveFnByForallExistUniqueStmt {
    pub fn_name: String,
    pub forall: ForallFact,
    pub line_file: LineFile,
}

// have by exist a R st {$p(a)}: a
#[derive(Clone)]
pub struct HaveByExistStmt {
    pub equal_tos: Vec<String>,
    pub exist_fact_in_have_obj_st: ExistFactEnum,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct HaveObjEqualStmt {
    pub param_def: ParamDefWithType,
    pub objs_equal_to: Vec<Obj>,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct HaveObjInNonemptySetOrParamTypeStmt {
    pub param_def: ParamDefWithType,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct DefLetStmt {
    pub param_def: ParamDefWithType,
    pub facts: Vec<Fact>,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct DefPropStmt {
    pub name: String,
    pub params_def_with_type: ParamDefWithType,
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

impl DefPropStmt {
    pub fn new(
        name: String,
        params_def_with_type: ParamDefWithType,
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
                braced_string(&self.params_def_with_type)
            ),
            _ => write!(
                f,
                "{} {}{}{}\n{}",
                PROP,
                self.name,
                braced_string(&self.params_def_with_type),
                COLON,
                vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.iff_facts, 1)
            ),
        }
    }
}

impl DefLetStmt {
    pub fn new(param_def: ParamDefWithType, facts: Vec<Fact>, line_file: LineFile) -> Self {
        DefLetStmt {
            param_def,
            facts,
            line_file,
        }
    }
}

impl fmt::Display for DefLetStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let param_str = self.param_def.to_string();
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
    pub fn new(param_def: ParamDefWithType, line_file: LineFile) -> Self {
        HaveObjInNonemptySetOrParamTypeStmt {
            param_def,
            line_file,
        }
    }
}

impl fmt::Display for HaveObjInNonemptySetOrParamTypeStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}", HAVE, self.param_def.to_string())
    }
}

impl HaveObjEqualStmt {
    pub fn new(param_def: ParamDefWithType, objs_equal_to: Vec<Obj>, line_file: LineFile) -> Self {
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
            self.param_def.to_string(),
            EQUAL,
            vec_to_string_join_by_comma(&self.objs_equal_to)
        )
    }
}

impl HaveByExistStmt {
    pub fn new(
        equal_tos: Vec<String>,
        exist_fact_in_have_obj_st: ExistFactEnum,
        line_file: LineFile,
    ) -> Self {
        HaveByExistStmt {
            equal_tos,
            exist_fact_in_have_obj_st,
            line_file,
        }
    }
}

impl fmt::Display for HaveByExistStmt {
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
    pub fn new(name: String, equal_to_anonymous_fn: AnonymousFn, line_file: LineFile) -> Self {
        HaveFnEqualStmt {
            name,
            equal_to_anonymous_fn,
            line_file,
        }
    }
}

impl fmt::Display for HaveFnEqualStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let fn_set_clause = FnSetClause::new(
            self.equal_to_anonymous_fn.body.params_def_with_set.clone(),
            self.equal_to_anonymous_fn.body.dom_facts.clone(),
            (*self.equal_to_anonymous_fn.body.ret_set).clone(),
        )
        .expect("anonymous function signature was already validated");
        write!(
            f,
            "{} {} {}{} {} {}",
            HAVE,
            FN_LOWER_CASE,
            self.name,
            brace_vec_colon_vec_to_string(
                &fn_set_clause.params_def_with_set,
                &fn_set_clause.dom_facts
            ),
            EQUAL,
            self.equal_to_anonymous_fn.equal_to
        )
    }
}

impl HaveFnByForallExistUniqueStmt {
    pub fn new(fn_name: String, forall: ForallFact, line_file: LineFile) -> Self {
        HaveFnByForallExistUniqueStmt {
            fn_name,
            forall,
            line_file,
        }
    }
}

impl fmt::Display for HaveFnByForallExistUniqueStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} {} {} {} {}{}\n{}",
            HAVE,
            FN_LOWER_CASE,
            self.fn_name,
            AS,
            SET,
            COLON,
            to_string_and_add_four_spaces_at_beginning_of_each_line(&self.forall, 1)
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
                    &format!("{} {}{} {}", CASE, case, COLON, self.equal_tos[i]),
                    1,
                )
            })
            .collect::<Vec<String>>();

        write!(
            f,
            "{} {} {}{} {} {} {}{}\n{}",
            HAVE,
            FN_LOWER_CASE,
            self.name,
            brace_vec_colon_vec_to_string(
                &self.fn_set_clause.params_def_with_set,
                &self.fn_set_clause.dom_facts
            ),
            self.fn_set_clause.ret_set,
            BY,
            CASES,
            COLON,
            vec_to_string_with_sep(&cases_and_proofs, "\n".to_string())
        )
    }
}

impl HaveFnEqualCaseByCaseStmt {
    pub fn new(
        name: String,
        fn_set_clause: FnSetClause,
        cases: Vec<AndChainAtomicFact>,
        equal_tos: Vec<Obj>,
        line_file: LineFile,
    ) -> Self {
        HaveFnEqualCaseByCaseStmt {
            name,
            fn_set_clause,
            cases,
            equal_tos,
            line_file,
        }
    }
}

pub fn induc_obj_plus_offset(induc_from: &Obj, offset: usize) -> Obj {
    if offset == 0 {
        induc_from.clone()
    } else {
        Add::new(induc_from.clone(), Number::new(offset.to_string()).into()).into()
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

impl HaveFnByInducCase {
    pub fn new(case_fact: AndChainAtomicFact, body: HaveFnByInducCaseBody) -> Self {
        HaveFnByInducCase { case_fact, body }
    }
}

impl HaveFnByInducStmt {
    pub fn new(
        name: String,
        fn_set_clause: FnSetClause,
        measure: Obj,
        lower_bound: Obj,
        cases: Vec<HaveFnByInducCase>,
        line_file: LineFile,
    ) -> Self {
        HaveFnByInducStmt {
            name,
            fn_set_clause,
            measure,
            lower_bound,
            cases,
            line_file,
        }
    }

    pub fn param_names(&self) -> Vec<String> {
        ParamGroupWithSet::collect_param_names(&self.fn_set_clause.params_def_with_set)
    }

    /// Flatten nested cases into the ordinary case-by-case shape used for stored forall facts.
    pub fn to_have_fn_equal_case_by_case_stmt(&self) -> HaveFnEqualCaseByCaseStmt {
        let line_file = self.line_file.clone();
        let mut cases: Vec<AndChainAtomicFact> = Vec::new();
        let mut equal_tos: Vec<Obj> = Vec::new();
        Self::flatten_case_list(&self.cases, None, &mut cases, &mut equal_tos, &line_file);
        HaveFnEqualCaseByCaseStmt::new(
            self.name.clone(),
            self.fn_set_clause.clone(),
            cases,
            equal_tos,
            line_file,
        )
    }

    fn flatten_case_list(
        source_cases: &[HaveFnByInducCase],
        prefix: Option<AndChainAtomicFact>,
        cases: &mut Vec<AndChainAtomicFact>,
        equal_tos: &mut Vec<Obj>,
        line_file: &LineFile,
    ) {
        for c in source_cases {
            let merged = match &prefix {
                Some(p) => {
                    merge_two_and_chain_clauses(p.clone(), c.case_fact.clone(), line_file.clone())
                }
                None => c.case_fact.clone(),
            };
            match &c.body {
                HaveFnByInducCaseBody::EqualTo(eq) => {
                    cases.push(merged);
                    equal_tos.push(eq.clone());
                }
                HaveFnByInducCaseBody::NestedCases(nested) => {
                    Self::flatten_case_list(nested, Some(merged), cases, equal_tos, line_file);
                }
            }
        }
    }
}

impl fmt::Display for HaveFnByInducStmt {
    /// Display uses the same parameter names as in source.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} {} {}{} {} {} {} {} {} {}{}",
            HAVE,
            FN_LOWER_CASE,
            self.name,
            brace_vec_colon_vec_to_string(
                &self.fn_set_clause.params_def_with_set,
                &self.fn_set_clause.dom_facts
            ),
            self.fn_set_clause.ret_set,
            BY,
            DECREASING,
            self.measure,
            FROM,
            self.lower_bound,
            COLON
        )?;
        Self::fmt_cases(f, &self.cases, 1)
    }
}

impl HaveFnByInducStmt {
    fn fmt_cases(
        f: &mut fmt::Formatter<'_>,
        cases: &[HaveFnByInducCase],
        indent: usize,
    ) -> fmt::Result {
        let pad = "    ".repeat(indent);
        for c in cases {
            writeln!(f)?;
            match &c.body {
                HaveFnByInducCaseBody::EqualTo(eq) => {
                    write!(f, "{}{} {}: {}", pad, CASE, c.case_fact, eq)?;
                }
                HaveFnByInducCaseBody::NestedCases(nested) => {
                    write!(f, "{}{} {}:", pad, CASE, c.case_fact)?;
                    Self::fmt_cases(f, nested, indent + 1)?;
                }
            }
        }
        Ok(())
    }
}

impl DefFamilyStmt {
    pub fn new(
        name: String,
        params_def_with_type: ParamDefWithType,
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
            self.params_def_with_type.to_string(),
            COLON,
            vec_to_string_join_by_comma(&self.dom_facts),
            RIGHT_BRACE,
            EQUAL,
            self.equal_to
        )
    }
}
