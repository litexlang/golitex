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

// The induction measure and lower bound must both be provably integer-valued.
// have fn f(a Z, b Z: a >= 0, b >= 0) R
//     by induc abs(a) + abs(b) from 0:
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
    pub prove_process: Vec<Stmt>,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct HaveTupleStmt {
    pub name: String,
    pub index_name: String,
    pub dimension: Obj,
    pub value: Obj,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct HaveCartStmt {
    pub name: String,
    pub index_name: String,
    pub dimension: Obj,
    pub value: Obj,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct HaveSeqStmt {
    pub name: String,
    pub seq_set: SeqSet,
    pub index_name: String,
    pub value: Obj,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct HaveFiniteSeqStmt {
    pub name: String,
    pub finite_seq_set: FiniteSeqSet,
    pub index_name: String,
    pub bound: Obj,
    pub value: Obj,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct HaveMatrixStmt {
    pub name: String,
    pub matrix_set: MatrixSet,
    pub row_index_name: String,
    pub row_bound: Obj,
    pub col_index_name: String,
    pub col_bound: Obj,
    pub value: Obj,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct DefTemplateStmt {
    pub template_name: String,
    pub template_arg_def: ParamDefWithType,
    pub template_arg_dom: Vec<OrAndChainAtomicFact>,
    pub template_def_stmt: TemplateDefEnum,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub enum TemplateDefEnum {
    HaveObjInNonemptySetStmt(HaveObjInNonemptySetOrParamTypeStmt),
    HaveObjEqualStmt(HaveObjEqualStmt),
    HaveObjByExistFactsStmt(HaveObjByExistFactsStmt),
    TrustHaveStmt(TrustHaveStmt),
    HaveByExistStmt(HaveByExistStmt),
    HaveFnEqualStmt(HaveFnEqualStmt),
    HaveFnEqualCaseByCaseStmt(HaveFnEqualCaseByCaseStmt),
    HaveFnByInducStmt(HaveFnByInducStmt),
    HaveFnByForallExistUniqueStmt(HaveFnByForallExistUniqueStmt),
    HaveTupleStmt(HaveTupleStmt),
    HaveCartStmt(HaveCartStmt),
    HaveSeqStmt(HaveSeqStmt),
    HaveFiniteSeqStmt(HaveFiniteSeqStmt),
    HaveMatrixStmt(HaveMatrixStmt),
}

// obtain a from exist x R st {$p(x)}
#[derive(Clone)]
pub struct HaveByExistStmt {
    pub equal_tos: Vec<String>,
    pub exist_fact_in_have_obj_st: ExistFactEnum,
    pub line_file: LineFile,
}

// have by preimage x from z $in fn_range(f)
#[derive(Clone)]
pub struct HaveByPreimageStmt {
    pub preimage_names: Vec<String>,
    pub range_membership: InFact,
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
pub struct HaveObjByExistFactsStmt {
    pub param_def: ParamDefWithType,
    pub facts: Vec<ExistBodyFact>,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct TrustHaveStmt {
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

impl TrustHaveStmt {
    pub fn new(param_def: ParamDefWithType, facts: Vec<Fact>, line_file: LineFile) -> Self {
        TrustHaveStmt {
            param_def,
            facts,
            line_file,
        }
    }

    pub fn store_reason() -> &'static str {
        "unproved object definition"
    }

    pub fn strict_mode_rejection_message() -> &'static str {
        "strict mode rejects user trust have statements; use have/claim/thm with a `?` goal or move trusted background into an imported module"
    }
}

impl fmt::Display for TrustHaveStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let param_str = self.param_def.to_string();
        match self.facts.len() {
            0 => write!(f, "{} {} {}", TRUST, HAVE, param_str),
            _ => write!(
                f,
                "{} {}{}\n{}",
                format!("{} {}", TRUST, HAVE),
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

    pub fn store_reason() -> &'static str {
        "object definition"
    }
}

impl fmt::Display for HaveObjInNonemptySetOrParamTypeStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}", HAVE, self.param_def.to_string())
    }
}

impl HaveObjByExistFactsStmt {
    pub fn new(
        param_def: ParamDefWithType,
        facts: Vec<ExistBodyFact>,
        line_file: LineFile,
    ) -> Self {
        HaveObjByExistFactsStmt {
            param_def,
            facts,
            line_file,
        }
    }

    pub fn store_reason() -> &'static str {
        HaveByExistStmt::store_reason()
    }
}

impl fmt::Display for HaveObjByExistFactsStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} {}{}\n{}",
            HAVE,
            self.param_def,
            COLON,
            vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.facts, 1)
        )
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

    pub fn store_reason() -> &'static str {
        HaveObjInNonemptySetOrParamTypeStmt::store_reason()
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

impl HaveTupleStmt {
    pub fn new(
        name: String,
        index_name: String,
        dimension: Obj,
        value: Obj,
        line_file: LineFile,
    ) -> Self {
        HaveTupleStmt {
            name,
            index_name,
            dimension,
            value,
            line_file,
        }
    }

    pub fn store_reason() -> &'static str {
        "tuple definition"
    }
}

impl fmt::Display for HaveTupleStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} {} {} {} {} {} {}, {}[{}] {} {}",
            HAVE,
            TUPLE,
            self.name,
            FOR,
            self.index_name,
            LESS_EQUAL,
            self.dimension,
            self.name,
            self.index_name,
            EQUAL,
            self.value
        )
    }
}

impl HaveCartStmt {
    pub fn new(
        name: String,
        index_name: String,
        dimension: Obj,
        value: Obj,
        line_file: LineFile,
    ) -> Self {
        HaveCartStmt {
            name,
            index_name,
            dimension,
            value,
            line_file,
        }
    }

    pub fn store_reason() -> &'static str {
        "cart definition"
    }
}

impl fmt::Display for HaveCartStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} {} {} {} {} {} {}, {}({}, {}) {} {}",
            HAVE,
            CART,
            self.name,
            FOR,
            self.index_name,
            LESS_EQUAL,
            self.dimension,
            PROJ,
            self.name,
            self.index_name,
            EQUAL,
            self.value
        )
    }
}

impl HaveSeqStmt {
    pub fn new(
        name: String,
        seq_set: SeqSet,
        index_name: String,
        value: Obj,
        line_file: LineFile,
    ) -> Self {
        HaveSeqStmt {
            name,
            seq_set,
            index_name,
            value,
            line_file,
        }
    }

    pub fn store_reason() -> &'static str {
        "sequence definition"
    }
}

impl fmt::Display for HaveSeqStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} {} {} {} {} {}, {}({}) {} {}",
            HAVE,
            SEQ,
            self.name,
            self.seq_set,
            FOR,
            self.index_name,
            self.name,
            self.index_name,
            EQUAL,
            self.value
        )
    }
}

impl HaveFiniteSeqStmt {
    pub fn new(
        name: String,
        finite_seq_set: FiniteSeqSet,
        index_name: String,
        bound: Obj,
        value: Obj,
        line_file: LineFile,
    ) -> Self {
        HaveFiniteSeqStmt {
            name,
            finite_seq_set,
            index_name,
            bound,
            value,
            line_file,
        }
    }

    pub fn store_reason() -> &'static str {
        "finite sequence definition"
    }
}

impl fmt::Display for HaveFiniteSeqStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} {} {} {} {} {} {} {}, {}({}) {} {}",
            HAVE,
            FINITE_SEQ,
            self.name,
            self.finite_seq_set,
            FOR,
            self.index_name,
            LESS_EQUAL,
            self.bound,
            self.name,
            self.index_name,
            EQUAL,
            self.value
        )
    }
}

impl HaveMatrixStmt {
    pub fn new(
        name: String,
        matrix_set: MatrixSet,
        row_index_name: String,
        row_bound: Obj,
        col_index_name: String,
        col_bound: Obj,
        value: Obj,
        line_file: LineFile,
    ) -> Self {
        HaveMatrixStmt {
            name,
            matrix_set,
            row_index_name,
            row_bound,
            col_index_name,
            col_bound,
            value,
            line_file,
        }
    }

    pub fn store_reason() -> &'static str {
        "matrix definition"
    }
}

impl fmt::Display for HaveMatrixStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} {} {} {} {} {} {} {}, {} {} {}, {}({}, {}) {} {}",
            HAVE,
            MATRIX,
            self.name,
            self.matrix_set,
            FOR,
            self.row_index_name,
            LESS_EQUAL,
            self.row_bound,
            self.col_index_name,
            LESS_EQUAL,
            self.col_bound,
            self.name,
            self.row_index_name,
            self.col_index_name,
            EQUAL,
            self.value
        )
    }
}

impl HaveObjInNonemptySetOrParamTypeStmt {
    pub fn single_defined_name(&self) -> Option<String> {
        let names = self.param_def.collect_param_names();
        if names.len() == 1 {
            Some(names[0].clone())
        } else {
            None
        }
    }
}

impl HaveObjByExistFactsStmt {
    pub fn single_defined_name(&self) -> Option<String> {
        let names = self.param_def.collect_param_names();
        if names.len() == 1 {
            Some(names[0].clone())
        } else {
            None
        }
    }
}

impl HaveObjEqualStmt {
    pub fn single_defined_name(&self) -> Option<String> {
        let names = self.param_def.collect_param_names();
        if names.len() == 1 {
            Some(names[0].clone())
        } else {
            None
        }
    }
}

impl TrustHaveStmt {
    pub fn single_defined_name(&self) -> Option<String> {
        let names = self.param_def.collect_param_names();
        if names.len() == 1 {
            Some(names[0].clone())
        } else {
            None
        }
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

    pub fn store_reason() -> &'static str {
        "exist elimination"
    }
}

impl fmt::Display for HaveByExistStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} {} {} {}",
            OBTAIN,
            vec_to_string_join_by_comma(&self.equal_tos),
            FROM,
            self.exist_fact_in_have_obj_st,
        )
    }
}

impl HaveByPreimageStmt {
    pub fn new(preimage_names: Vec<String>, range_membership: InFact, line_file: LineFile) -> Self {
        HaveByPreimageStmt {
            preimage_names,
            range_membership,
            line_file,
        }
    }
}

impl fmt::Display for HaveByPreimageStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} {} {} {} {} {}",
            HAVE,
            BY,
            PREIMAGE,
            vec_to_string_join_by_comma(&self.preimage_names),
            FROM,
            self.range_membership,
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

    pub fn store_reason() -> &'static str {
        "function definition"
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
    pub fn new(
        fn_name: String,
        forall: ForallFact,
        prove_process: Vec<Stmt>,
        line_file: LineFile,
    ) -> Self {
        HaveFnByForallExistUniqueStmt {
            fn_name,
            forall,
            prove_process,
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
            to_string_and_add_four_spaces_at_beginning_of_each_line(
                &format!("{} {}", QUESTION_GOAL, self.forall),
                1,
            )
        )?;
        if !self.prove_process.is_empty() {
            write!(
                f,
                "\n{}",
                vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.prove_process, 1)
            )?;
        }
        Ok(())
    }
}

impl DefTemplateStmt {
    pub fn new(
        template_name: String,
        template_arg_def: ParamDefWithType,
        template_arg_dom: Vec<OrAndChainAtomicFact>,
        template_def_stmt: TemplateDefEnum,
        line_file: LineFile,
    ) -> Self {
        DefTemplateStmt {
            template_name,
            template_arg_def,
            template_arg_dom,
            template_def_stmt,
            line_file,
        }
    }
}

impl TemplateDefEnum {
    pub fn defined_name(&self) -> Option<String> {
        match self {
            TemplateDefEnum::HaveObjInNonemptySetStmt(stmt) => stmt.single_defined_name(),
            TemplateDefEnum::HaveObjEqualStmt(stmt) => stmt.single_defined_name(),
            TemplateDefEnum::HaveObjByExistFactsStmt(stmt) => stmt.single_defined_name(),
            TemplateDefEnum::TrustHaveStmt(stmt) => stmt.single_defined_name(),
            TemplateDefEnum::HaveByExistStmt(stmt) => {
                if stmt.equal_tos.len() == 1 {
                    Some(stmt.equal_tos[0].clone())
                } else {
                    None
                }
            }
            TemplateDefEnum::HaveFnEqualStmt(stmt) => Some(stmt.name.clone()),
            TemplateDefEnum::HaveFnEqualCaseByCaseStmt(stmt) => Some(stmt.name.clone()),
            TemplateDefEnum::HaveFnByInducStmt(stmt) => Some(stmt.name.clone()),
            TemplateDefEnum::HaveFnByForallExistUniqueStmt(stmt) => Some(stmt.fn_name.clone()),
            TemplateDefEnum::HaveTupleStmt(stmt) => Some(stmt.name.clone()),
            TemplateDefEnum::HaveCartStmt(stmt) => Some(stmt.name.clone()),
            TemplateDefEnum::HaveSeqStmt(stmt) => Some(stmt.name.clone()),
            TemplateDefEnum::HaveFiniteSeqStmt(stmt) => Some(stmt.name.clone()),
            TemplateDefEnum::HaveMatrixStmt(stmt) => Some(stmt.name.clone()),
        }
    }

    pub fn to_stmt(&self) -> Stmt {
        match self {
            TemplateDefEnum::HaveObjInNonemptySetStmt(stmt) => stmt.clone().into(),
            TemplateDefEnum::HaveObjEqualStmt(stmt) => stmt.clone().into(),
            TemplateDefEnum::HaveObjByExistFactsStmt(stmt) => stmt.clone().into(),
            TemplateDefEnum::TrustHaveStmt(stmt) => stmt.clone().into(),
            TemplateDefEnum::HaveByExistStmt(stmt) => stmt.clone().into(),
            TemplateDefEnum::HaveFnEqualStmt(stmt) => stmt.clone().into(),
            TemplateDefEnum::HaveFnEqualCaseByCaseStmt(stmt) => stmt.clone().into(),
            TemplateDefEnum::HaveFnByInducStmt(stmt) => stmt.clone().into(),
            TemplateDefEnum::HaveFnByForallExistUniqueStmt(stmt) => stmt.clone().into(),
            TemplateDefEnum::HaveTupleStmt(stmt) => stmt.clone().into(),
            TemplateDefEnum::HaveCartStmt(stmt) => stmt.clone().into(),
            TemplateDefEnum::HaveSeqStmt(stmt) => stmt.clone().into(),
            TemplateDefEnum::HaveFiniteSeqStmt(stmt) => stmt.clone().into(),
            TemplateDefEnum::HaveMatrixStmt(stmt) => stmt.clone().into(),
        }
    }
}

impl fmt::Display for TemplateDefEnum {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TemplateDefEnum::HaveObjInNonemptySetStmt(stmt) => write!(f, "{}", stmt),
            TemplateDefEnum::HaveObjEqualStmt(stmt) => write!(f, "{}", stmt),
            TemplateDefEnum::HaveObjByExistFactsStmt(stmt) => write!(f, "{}", stmt),
            TemplateDefEnum::TrustHaveStmt(stmt) => write!(f, "{}", stmt),
            TemplateDefEnum::HaveByExistStmt(stmt) => write!(f, "{}", stmt),
            TemplateDefEnum::HaveFnEqualStmt(stmt) => write!(f, "{}", stmt),
            TemplateDefEnum::HaveFnEqualCaseByCaseStmt(stmt) => write!(f, "{}", stmt),
            TemplateDefEnum::HaveFnByInducStmt(stmt) => write!(f, "{}", stmt),
            TemplateDefEnum::HaveFnByForallExistUniqueStmt(stmt) => write!(f, "{}", stmt),
            TemplateDefEnum::HaveTupleStmt(stmt) => write!(f, "{}", stmt),
            TemplateDefEnum::HaveCartStmt(stmt) => write!(f, "{}", stmt),
            TemplateDefEnum::HaveSeqStmt(stmt) => write!(f, "{}", stmt),
            TemplateDefEnum::HaveFiniteSeqStmt(stmt) => write!(f, "{}", stmt),
            TemplateDefEnum::HaveMatrixStmt(stmt) => write!(f, "{}", stmt),
        }
    }
}

impl fmt::Display for DefTemplateStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}{}{}{}{}{}\n{}",
            TEMPLATE,
            LESS,
            self.template_arg_def,
            if self.template_arg_dom.is_empty() {
                String::new()
            } else {
                format!(
                    "{} {}",
                    COLON,
                    vec_to_string_join_by_comma(&self.template_arg_dom)
                )
            },
            GREATER,
            COLON,
            to_string_and_add_four_spaces_at_beginning_of_each_line(&self.template_def_stmt, 1)
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
            "{} {} {}{} {} {} {} {}\n{}",
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

    pub fn store_reason() -> &'static str {
        HaveFnEqualStmt::store_reason()
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
            "{} {} {}{} {} {} {} {} {} {}",
            HAVE,
            FN_LOWER_CASE,
            self.name,
            brace_vec_colon_vec_to_string(
                &self.fn_set_clause.params_def_with_set,
                &self.fn_set_clause.dom_facts
            ),
            self.fn_set_clause.ret_set,
            BY,
            INDUC,
            self.measure,
            FROM,
            self.lower_bound
        )?;
        write!(f, "{}", COLON)?;
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
